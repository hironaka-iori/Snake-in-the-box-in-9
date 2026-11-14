import PartitionData205_213
namespace PartitionCover205_213
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,2,7,10,11,12,13,14,15,16,17])
    (d9 : a 9 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d10 : a 10 ∈ [0,2])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    : a 25 ∈ [0,2,7,10,12,14] ∧ a 14 ∈ [0,2,13,14,15,16,17] := by
  have b0 : a 25 ≠ 11 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,2,7,10,12,13,14,15,16,17] := remove (a 25) 11 [0,2,7,10,11,12,13,14,15,16,17] d25 b0
  have b1 : a 25 ≠ 13 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,2,7,10,12,14,15,16,17] := remove (a 25) 13 [0,2,7,10,12,13,14,15,16,17] t0 b1
  have b2 : a 25 ≠ 15 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 15 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,7,10,12,14,16,17] := remove (a 25) 15 [0,2,7,10,12,14,15,16,17] t1 b2
  have b3 : a 25 ≠ 16 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,7,10,12,14,17] := remove (a 25) 16 [0,2,7,10,12,14,16,17] t2 b3
  have b4 : a 25 ≠ 17 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 17 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,7,10,12,14] := remove (a 25) 17 [0,2,7,10,12,14,17] t3 b4
  have b5 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b5
  have b6 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 14 ≠ 6 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 6 d10 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 14 ≠ 7 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 7 d10 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,2,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 14 ≠ 8 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 8 d10 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,2,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 14 ≠ 9 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 9 d10 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0,2,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,2,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 14 ≠ 10 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 10 d10 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,11,12,13,14,15,16,17] := remove (a 14) 10 [0,2,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 14 ≠ 11 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,12,13,14,15,16,17] := remove (a 14) 11 [0,2,11,12,13,14,15,16,17] t13 b14
  have b15 : a 14 ≠ 12 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 12 d10 c36 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,13,14,15,16,17] := remove (a 14) 12 [0,2,12,13,14,15,16,17] t14 b15
  exact And.intro t4 (t15)

theorem chunk13 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,13,14,15,16,17])
    (d10 : a 10 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,8])
    (d15 : a 15 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 14 ∈ [0,2] ∧ a 26 ∈ [0,2,3,5] ∧ a 11 ∈ [0] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 14 ≠ 13 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 13 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,14,15,16,17] := remove (a 14) 13 [0,2,13,14,15,16,17] d14 b0
  have b1 : a 14 ≠ 14 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 14 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,15,16,17] := remove (a 14) 14 [0,2,14,15,16,17] t0 b1
  have b2 : a 14 ≠ 15 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 15 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,2,16,17] := remove (a 14) 15 [0,2,15,16,17] t1 b2
  have b3 : a 14 ≠ 16 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 16 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,17] := remove (a 14) 16 [0,2,16,17] t2 b3
  have b4 : a 14 ≠ 17 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 17 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,2] := remove (a 14) 17 [0,2,17] t3 b4
  have b5 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b5
  have b6 : a 26 ≠ 4 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 26) 4 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 26 ≠ 6 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,3,5,7,8,9,10,11] := remove (a 26) 6 [0,2,3,5,6,7,8,9,10,11] t6 b7
  have b8 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,3,5,8,9,10,11] := remove (a 26) 7 [0,2,3,5,7,8,9,10,11] t7 b8
  have b9 : a 26 ≠ 8 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,3,5,9,10,11] := remove (a 26) 8 [0,2,3,5,8,9,10,11] t8 b9
  have b10 : a 26 ≠ 9 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,2,3,5,10,11] := remove (a 26) 9 [0,2,3,5,9,10,11] t9 b10
  have b11 : a 26 ≠ 10 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,3,5,11] := remove (a 26) 10 [0,2,3,5,10,11] t10 b11
  have b12 : a 26 ≠ 11 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3,5] := remove (a 26) 11 [0,2,3,5,11] t11 b12
  have b13 : a 11 ≠ 8 := exclude [0,1] (edge r38) (a 11) (a 15) 8 d15 c38 (by decide +kernel)
  have t13 : a 11 ∈ [0] := remove (a 11) 8 [0,8] d11 b13
  have b14 : a 15 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 1 t13 c38 (by decide +kernel)
  have t14 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b14
  have b15 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 t13 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d27 b15
  exact And.intro t4 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))

theorem chunk14 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d11 : a 11 ∈ [0])
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 27 ∈ [0] := by
  have b0 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d27 b0
  have b1 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 7 [0,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,9,10,11,12,13,14,15,16,17] := remove (a 27) 8 [0,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,10,11,12,13,14,15,16,17] := remove (a 27) 9 [0,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 27 ≠ 10 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,11,12,13,14,15,16,17] := remove (a 27) 10 [0,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 27 ≠ 11 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,12,13,14,15,16,17] := remove (a 27) 11 [0,11,12,13,14,15,16,17] t8 b9
  have b10 : a 27 ≠ 12 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 12 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,13,14,15,16,17] := remove (a 27) 12 [0,12,13,14,15,16,17] t9 b10
  have b11 : a 27 ≠ 13 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 13 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,14,15,16,17] := remove (a 27) 13 [0,13,14,15,16,17] t10 b11
  have b12 : a 27 ≠ 14 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 14 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,15,16,17] := remove (a 27) 14 [0,14,15,16,17] t11 b12
  have b13 : a 27 ≠ 15 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 15 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,16,17] := remove (a 27) 15 [0,15,16,17] t12 b13
  have b14 : a 27 ≠ 16 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 16 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,17] := remove (a 27) 16 [0,16,17] t13 b14
  have b15 : a 27 ≠ 17 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 17 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0] := remove (a 27) 17 [0,17] t14 b15
  exact t15

theorem chunk15 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d14 : a 14 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 12 ∈ [0] ∧ a 14 ∈ [0] ∧ a 28 ∈ [0,1,16,17] := by
  have b0 : a 12 ≠ 1 := exclude [0] (edge r40) (a 12) (a 13) 1 d13 c40 (by decide +kernel)
  have t0 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b0
  have b1 : a 14 ≠ 2 := exclude [0] (fun u v => edge r41 v u) (a 14) (a 12) 2 t0 c41 (by decide +kernel)
  have t1 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b1
  have b2 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 t0 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d28 b2
  have b3 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 t0 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 t0 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 t0 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 t0 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 t0 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 t0 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 28) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 t0 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 28) 9 [0,1,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 28 ≠ 10 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 10 t0 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 28) 10 [0,1,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 28 ≠ 11 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 11 t0 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,1,12,13,14,15,16,17] := remove (a 28) 11 [0,1,11,12,13,14,15,16,17] t10 b11
  have b12 : a 28 ≠ 12 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 12 t0 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,1,13,14,15,16,17] := remove (a 28) 12 [0,1,12,13,14,15,16,17] t11 b12
  have b13 : a 28 ≠ 13 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 13 t0 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,1,14,15,16,17] := remove (a 28) 13 [0,1,13,14,15,16,17] t12 b13
  have b14 : a 28 ≠ 14 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 14 t0 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,1,15,16,17] := remove (a 28) 14 [0,1,14,15,16,17] t13 b14
  have b15 : a 28 ≠ 15 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 15 t0 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,1,16,17] := remove (a 28) 15 [0,1,15,16,17] t14 b15
  exact And.intro t0 (And.intro t1 (t15))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_213
