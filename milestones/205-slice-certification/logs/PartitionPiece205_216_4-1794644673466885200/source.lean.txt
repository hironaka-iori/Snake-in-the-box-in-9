import PartitionData205_216
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,6,12])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 13 ∈ [0,2,3] ∧ a 25 ∈ [0,1,7] := by
  have b0 : a 13 ≠ 1 := exclude [0,6,12] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t0 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b0
  have b1 : a 25 ≠ 2 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d25 b1
  have b2 : a 25 ≠ 3 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 25 ≠ 4 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 25 ≠ 5 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 25 ≠ 6 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 25 ≠ 8 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,7,9,10,11,12,13,14,15,16,17] := remove (a 25) 8 [0,1,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 25 ≠ 9 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,7,10,11,12,13,14,15,16,17] := remove (a 25) 9 [0,1,7,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 25 ≠ 10 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,7,11,12,13,14,15,16,17] := remove (a 25) 10 [0,1,7,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 25 ≠ 11 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,7,12,13,14,15,16,17] := remove (a 25) 11 [0,1,7,11,12,13,14,15,16,17] t8 b9
  have b10 : a 25 ≠ 12 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,7,13,14,15,16,17] := remove (a 25) 12 [0,1,7,12,13,14,15,16,17] t9 b10
  have b11 : a 25 ≠ 13 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,7,14,15,16,17] := remove (a 25) 13 [0,1,7,13,14,15,16,17] t10 b11
  have b12 : a 25 ≠ 14 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 14 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,7,15,16,17] := remove (a 25) 14 [0,1,7,14,15,16,17] t11 b12
  have b13 : a 25 ≠ 15 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 15 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,7,16,17] := remove (a 25) 15 [0,1,7,15,16,17] t12 b13
  have b14 : a 25 ≠ 16 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,7,17] := remove (a 25) 16 [0,1,7,16,17] t13 b14
  have b15 : a 25 ≠ 17 := exclude [0,6,12] (fun u v => edge r34 v u) (a 25) (a 9) 17 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,7] := remove (a 25) 17 [0,1,7,17] t14 b15
  exact And.intro t0 (t15)

theorem chunk17 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,3])
    (d11 : a 11 ∈ [0,2,4])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,5,6,9,10,11])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 26 ∈ [0,1] ∧ a 15 ∈ [0,1,5,9,11] ∧ a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 10 ≠ 3 := exclude [0,2,4] (edge r35) (a 10) (a 11) 3 d11 c35 (by decide +kernel)
  have t0 : a 10 ∈ [0] := remove (a 10) 3 [0,3] d10 b0
  have b1 : a 11 ≠ 2 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 2 t0 c35 (by decide +kernel)
  have t1 : a 11 ∈ [0,4] := remove (a 11) 2 [0,2,4] d11 b1
  have b2 : a 11 ≠ 4 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 4 t0 c35 (by decide +kernel)
  have t2 : a 11 ∈ [0] := remove (a 11) 4 [0,4] t1 b2
  have b3 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t0 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b3
  have b4 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t0 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 26) 3 [0,1,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t0 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 26) 4 [0,1,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 t0 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,6,7,8,9,10,11] := remove (a 26) 5 [0,1,5,6,7,8,9,10,11] t5 b6
  have b7 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 6 t0 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,7,8,9,10,11] := remove (a 26) 6 [0,1,6,7,8,9,10,11] t6 b7
  have b8 : a 26 ≠ 7 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 7 t0 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,8,9,10,11] := remove (a 26) 7 [0,1,7,8,9,10,11] t7 b8
  have b9 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 t0 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,9,10,11] := remove (a 26) 8 [0,1,8,9,10,11] t8 b9
  have b10 : a 26 ≠ 9 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 9 t0 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,10,11] := remove (a 26) 9 [0,1,9,10,11] t9 b10
  have b11 : a 26 ≠ 10 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 10 t0 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,11] := remove (a 26) 10 [0,1,10,11] t10 b11
  have b12 : a 26 ≠ 11 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 11 t0 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,1] := remove (a 26) 11 [0,1,11] t11 b12
  have b13 : a 15 ≠ 6 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 6 t2 c38 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,5,9,10,11] := remove (a 15) 6 [0,1,5,6,9,10,11] d15 b13
  have b14 : a 15 ≠ 10 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 10 t2 c38 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,5,9,11] := remove (a 15) 10 [0,1,5,9,10,11] t13 b14
  have b15 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 t2 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b15
  exact And.intro t0 (And.intro t2 (And.intro t12 (And.intro t14 (t15))))

theorem chunk18 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0])
    (d12 : a 12 ∈ [0,2,10,11,22,23])
    (d13 : a 13 ∈ [0,2,3])
    (d14 : a 14 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 27 ∈ [0,1] ∧ a 12 ∈ [0] ∧ a 28 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] d27 b0
  have b1 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t1 b2
  have b3 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,7,8,9,10,11] := remove (a 27) 6 [0,1,6,7,8,9,10,11] t2 b3
  have b4 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,8,9,10,11] := remove (a 27) 7 [0,1,7,8,9,10,11] t3 b4
  have b5 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,9,10,11] := remove (a 27) 8 [0,1,8,9,10,11] t4 b5
  have b6 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,10,11] := remove (a 27) 9 [0,1,9,10,11] t5 b6
  have b7 : a 27 ≠ 10 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,11] := remove (a 27) 10 [0,1,10,11] t6 b7
  have b8 : a 27 ≠ 11 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1] := remove (a 27) 11 [0,1,11] t7 b8
  have b9 : a 12 ≠ 2 := exclude [0,2,3] (edge r40) (a 12) (a 13) 2 d13 c40 (by decide +kernel)
  have t9 : a 12 ∈ [0,10,11,22,23] := remove (a 12) 2 [0,2,10,11,22,23] d12 b9
  have b10 : a 12 ≠ 10 := exclude [0,2,3] (edge r40) (a 12) (a 13) 10 d13 c40 (by decide +kernel)
  have t10 : a 12 ∈ [0,11,22,23] := remove (a 12) 10 [0,10,11,22,23] t9 b10
  have b11 : a 12 ≠ 23 := exclude [0,2,3] (edge r40) (a 12) (a 13) 23 d13 c40 (by decide +kernel)
  have t11 : a 12 ∈ [0,11,22] := remove (a 12) 23 [0,11,22,23] t10 b11
  have b12 : a 12 ≠ 11 := exclude [0] (edge r41) (a 12) (a 14) 11 d14 c41 (by decide +kernel)
  have t12 : a 12 ∈ [0,22] := remove (a 12) 11 [0,11,22] t11 b12
  have b13 : a 12 ≠ 22 := exclude [0] (edge r41) (a 12) (a 14) 22 d14 c41 (by decide +kernel)
  have t13 : a 12 ∈ [0] := remove (a 12) 22 [0,22] t12 b13
  have b14 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t13 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b14
  have b15 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 t13 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t8 (And.intro t13 (t15))

theorem chunk19 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d12 : a 12 ∈ [0])
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 28 ∈ [0,2,20,21,22,23] := by
  have b0 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b0
  have b1 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 28 ≠ 10 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 28 ≠ 11 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 28 ≠ 12 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 12 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,2,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 12 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 28 ≠ 13 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 13 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,2,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 13 [0,2,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 28 ≠ 14 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 14 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,15,16,17,18,19,20,21,22,23] := remove (a 28) 14 [0,2,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 28 ≠ 15 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 15 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,16,17,18,19,20,21,22,23] := remove (a 28) 15 [0,2,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 28 ≠ 16 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 16 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,17,18,19,20,21,22,23] := remove (a 28) 16 [0,2,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 28 ≠ 17 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 17 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,2,18,19,20,21,22,23] := remove (a 28) 17 [0,2,17,18,19,20,21,22,23] t12 b13
  have b14 : a 28 ≠ 18 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 18 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,19,20,21,22,23] := remove (a 28) 18 [0,2,18,19,20,21,22,23] t13 b14
  have b15 : a 28 ≠ 19 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 19 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,20,21,22,23] := remove (a 28) 19 [0,2,19,20,21,22,23] t14 b15
  exact t15

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_216
