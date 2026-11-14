import PartitionData205_191
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,10,13,19,20,21,22,23])
    (d11 : a 11 ∈ [0,4])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 15 ∈ [0,10,13,21] ∧ a 27 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := by
  have b0 : a 15 ≠ 19 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 19 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [0,10,13,20,21,22,23] := remove (a 15) 19 [0,10,13,19,20,21,22,23] d15 b0
  have b1 : a 15 ≠ 20 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 20 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [0,10,13,21,22,23] := remove (a 15) 20 [0,10,13,20,21,22,23] t0 b1
  have b2 : a 15 ≠ 22 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 22 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,10,13,21,23] := remove (a 15) 22 [0,10,13,21,22,23] t1 b2
  have b3 : a 15 ≠ 23 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 23 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,10,13,21] := remove (a 15) 23 [0,10,13,21,23] t2 b3
  have b4 : a 27 ≠ 6 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d27 b4
  have b5 : a 27 ≠ 7 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 27 ≠ 8 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 27 ≠ 9 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 27 ≠ 10 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 27 ≠ 11 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 27 ≠ 12 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 12 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 12 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 27 ≠ 13 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 13 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 27) 13 [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 27 ≠ 14 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 14 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] := remove (a 27) 14 [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 27 ≠ 15 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 15 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,2,3,4,5,16,17,18,19,20,21,22,23] := remove (a 27) 15 [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 27 ≠ 16 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 16 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := remove (a 27) 16 [0,1,2,3,4,5,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 27 ≠ 17 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 17 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := remove (a 27) 17 [0,1,2,3,4,5,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (t15)

theorem chunk13 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,2,3,4,5,18,19,20,21,22,23])
    (d11 : a 11 ∈ [0,4])
    (d12 : a 12 ∈ [0,12,16,20])
    (d13 : a 13 ∈ [0,1,2,6,7,8])
    (d28 : a 28 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 27 ∈ [0,1,2,3,4,5] ∧ a 12 ∈ [0,20] ∧ a 13 ∈ [0,6] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 27 ≠ 18 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 18 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,2,3,4,5,19,20,21,22,23] := remove (a 27) 18 [0,1,2,3,4,5,18,19,20,21,22,23] d27 b0
  have b1 : a 27 ≠ 19 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 19 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,2,3,4,5,20,21,22,23] := remove (a 27) 19 [0,1,2,3,4,5,19,20,21,22,23] t0 b1
  have b2 : a 27 ≠ 20 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 20 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,2,3,4,5,21,22,23] := remove (a 27) 20 [0,1,2,3,4,5,20,21,22,23] t1 b2
  have b3 : a 27 ≠ 21 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 21 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,2,3,4,5,22,23] := remove (a 27) 21 [0,1,2,3,4,5,21,22,23] t2 b3
  have b4 : a 27 ≠ 22 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 22 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,2,3,4,5,23] := remove (a 27) 22 [0,1,2,3,4,5,22,23] t3 b4
  have b5 : a 27 ≠ 23 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 23 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,2,3,4,5] := remove (a 27) 23 [0,1,2,3,4,5,23] t4 b5
  have b6 : a 12 ≠ 12 := exclude [0,1,2,6,7,8] (edge r40) (a 12) (a 13) 12 d13 c40 (by decide +kernel)
  have t6 : a 12 ∈ [0,16,20] := remove (a 12) 12 [0,12,16,20] d12 b6
  have b7 : a 12 ≠ 16 := exclude [0,1,2,6,7,8] (edge r40) (a 12) (a 13) 16 d13 c40 (by decide +kernel)
  have t7 : a 12 ∈ [0,20] := remove (a 12) 16 [0,16,20] t6 b7
  have b8 : a 13 ≠ 1 := exclude [0,20] (fun u v => edge r40 v u) (a 13) (a 12) 1 t7 c40 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,6,7,8] := remove (a 13) 1 [0,1,2,6,7,8] d13 b8
  have b9 : a 13 ≠ 2 := exclude [0,20] (fun u v => edge r40 v u) (a 13) (a 12) 2 t7 c40 (by decide +kernel)
  have t9 : a 13 ∈ [0,6,7,8] := remove (a 13) 2 [0,2,6,7,8] t8 b9
  have b10 : a 13 ≠ 7 := exclude [0,20] (fun u v => edge r40 v u) (a 13) (a 12) 7 t7 c40 (by decide +kernel)
  have t10 : a 13 ∈ [0,6,8] := remove (a 13) 7 [0,6,7,8] t9 b10
  have b11 : a 13 ≠ 8 := exclude [0,20] (fun u v => edge r40 v u) (a 13) (a 12) 8 t7 c40 (by decide +kernel)
  have t11 : a 13 ∈ [0,6] := remove (a 13) 8 [0,6,8] t10 b11
  have b12 : a 28 ≠ 1 := exclude [0,20] (fun u v => edge r42 v u) (a 28) (a 12) 1 t7 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b12
  have b13 : a 28 ≠ 2 := exclude [0,20] (fun u v => edge r42 v u) (a 28) (a 12) 2 t7 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,3] := remove (a 28) 2 [0,2,3] t12 b13
  have b14 : a 28 ≠ 3 := exclude [0,20] (fun u v => edge r42 v u) (a 28) (a 12) 3 t7 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0] := remove (a 28) 3 [0,3] t13 b14
  have b15 : a 29 ≠ 2 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 2 t11 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b15
  exact And.intro t5 (And.intro t7 (And.intro t11 (And.intro t14 (t15))))

theorem chunk14 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0,6])
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 29 ∈ [0,1,18,20,21,22,23] := by
  have b0 : a 29 ≠ 3 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 4 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 5 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 6 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 7 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 8 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 9 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 10 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 11 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 12 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 13 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 14 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,1,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 15 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,16,17,18,19,20,21,22,23] := remove (a 29) 15 [0,1,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 16 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,17,18,19,20,21,22,23] := remove (a 29) 16 [0,1,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 17 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,18,19,20,21,22,23] := remove (a 29) 17 [0,1,17,18,19,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 19 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,18,20,21,22,23] := remove (a 29) 19 [0,1,18,19,20,21,22,23] t14 b15
  exact t15

theorem chunk15 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,18,20,21,22,23])
    (d13 : a 13 ∈ [0,6])
    (d15 : a 15 ∈ [0,10,13,21])
    (d14 : a 14 ∈ [0,9])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,1,18,21] ∧ a 15 ∈ [0,21] ∧ a 30 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 20 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,18,21,22,23] := remove (a 29) 20 [0,1,18,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 22 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,18,21,23] := remove (a 29) 22 [0,1,18,21,22,23] t0 b1
  have b2 : a 29 ≠ 23 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,18,21] := remove (a 29) 23 [0,1,18,21,23] t1 b2
  have b3 : a 15 ≠ 10 := exclude [0,9] (fun u v => edge r45 v u) (a 15) (a 14) 10 d14 c45 (by decide +kernel)
  have t3 : a 15 ∈ [0,13,21] := remove (a 15) 10 [0,10,13,21] d15 b3
  have b4 : a 15 ≠ 13 := exclude [0,9] (fun u v => edge r45 v u) (a 15) (a 14) 13 d14 c45 (by decide +kernel)
  have t4 : a 15 ∈ [0,21] := remove (a 15) 13 [0,13,21] t3 b4
  have b5 : a 30 ≠ 2 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b5
  have b6 : a 30 ≠ 3 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 30 ≠ 6 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 30 ≠ 7 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 30 ≠ 8 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 30 ≠ 9 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 30 ≠ 10 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 10 [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 30 ≠ 11 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 11 [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 30 ≠ 12 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 12 [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 30 ≠ 13 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 13 [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 30 ≠ 14 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23] := remove (a 30) 14 [0,1,4,5,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t2 (And.intro t4 (t15))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_191
