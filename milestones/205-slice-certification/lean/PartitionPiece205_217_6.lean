import PartitionData205_217
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,7,10,11])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 26 ∈ [0,7] ∧ a 15 ∈ [0,1,3,4,9,11] ∧ a 27 ∈ [0,7,9,11] := by
  have b0 : a 26 ≠ 10 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,7,11] := remove (a 26) 10 [0,7,10,11] d26 b0
  have b1 : a 26 ≠ 11 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,7] := remove (a 26) 11 [0,7,11] t0 b1
  have b2 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b2
  have b3 : a 15 ≠ 5 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,3,4,6,7,8,9,10,11] := remove (a 15) 5 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 15 ≠ 6 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 6 d11 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,3,4,7,8,9,10,11] := remove (a 15) 6 [0,1,3,4,6,7,8,9,10,11] t3 b4
  have b5 : a 15 ≠ 7 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 7 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,3,4,8,9,10,11] := remove (a 15) 7 [0,1,3,4,7,8,9,10,11] t4 b5
  have b6 : a 15 ≠ 8 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 8 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,3,4,9,10,11] := remove (a 15) 8 [0,1,3,4,8,9,10,11] t5 b6
  have b7 : a 15 ≠ 10 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 10 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,3,4,9,11] := remove (a 15) 10 [0,1,3,4,9,10,11] t6 b7
  have b8 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b8
  have b9 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,5,6,7,8,9,10,11] := remove (a 27) 4 [0,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,6,7,8,9,10,11] := remove (a 27) 5 [0,5,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,7,8,9,10,11] := remove (a 27) 6 [0,6,7,8,9,10,11] t12 b13
  have b14 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,7,9,10,11] := remove (a 27) 8 [0,7,8,9,10,11] t13 b14
  have b15 : a 27 ≠ 10 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,7,9,11] := remove (a 27) 10 [0,7,9,10,11] t14 b15
  exact And.intro t1 (And.intro t7 (t15))

theorem chunk25 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,7,9,11])
    (d11 : a 11 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (d13 : a 13 ∈ [0,12])
    (d14 : a 14 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 27 ∈ [0,7,9] ∧ a 12 ∈ [0] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0] ∧ a 28 ∈ [0,8,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 27 ≠ 11 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,7,9] := remove (a 27) 11 [0,7,9,11] d27 b0
  have b1 : a 12 ≠ 1 := exclude [0,12] (edge r40) (a 12) (a 13) 1 d13 c40 (by decide +kernel)
  have t1 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b1
  have b2 : a 13 ≠ 12 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 12 t1 c40 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 12 [0,12] d13 b2
  have b3 : a 14 ≠ 2 := exclude [0] (fun u v => edge r41 v u) (a 14) (a 12) 2 t1 c41 (by decide +kernel)
  have t3 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b3
  have b4 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t1 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b4
  have b5 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 t1 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 t1 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 t1 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 t1 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 t1 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 t1 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 t1 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 9 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 28 ≠ 10 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 10 t1 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 10 [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 28 ≠ 11 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 11 t1 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 11 [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 28 ≠ 12 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 12 t1 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,8,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 12 [0,8,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 28 ≠ 13 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 13 t1 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,8,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 13 [0,8,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t15))))

theorem chunk26 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,8,14,15,16,17,18,19,20,21,22,23])
    (d12 : a 12 ∈ [0])
    (d15 : a 15 ∈ [0,1,3,4,9,11])
    (d13 : a 13 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 28 ∈ [0,8] ∧ a 15 ∈ [0] ∧ a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 28 ≠ 14 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 14 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,8,15,16,17,18,19,20,21,22,23] := remove (a 28) 14 [0,8,14,15,16,17,18,19,20,21,22,23] d28 b0
  have b1 : a 28 ≠ 15 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 15 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,8,16,17,18,19,20,21,22,23] := remove (a 28) 15 [0,8,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 28 ≠ 16 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 16 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,8,17,18,19,20,21,22,23] := remove (a 28) 16 [0,8,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 28 ≠ 17 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 17 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,8,18,19,20,21,22,23] := remove (a 28) 17 [0,8,17,18,19,20,21,22,23] t2 b3
  have b4 : a 28 ≠ 18 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 18 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,8,19,20,21,22,23] := remove (a 28) 18 [0,8,18,19,20,21,22,23] t3 b4
  have b5 : a 28 ≠ 19 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 19 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,8,20,21,22,23] := remove (a 28) 19 [0,8,19,20,21,22,23] t4 b5
  have b6 : a 28 ≠ 20 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 20 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,8,21,22,23] := remove (a 28) 20 [0,8,20,21,22,23] t5 b6
  have b7 : a 28 ≠ 21 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 21 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,8,22,23] := remove (a 28) 21 [0,8,21,22,23] t6 b7
  have b8 : a 28 ≠ 22 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 22 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,8,23] := remove (a 28) 22 [0,8,22,23] t7 b8
  have b9 : a 28 ≠ 23 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 23 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,8] := remove (a 28) 23 [0,8,23] t8 b9
  have b10 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 d13 c43 (by decide +kernel)
  have t10 : a 15 ∈ [0,3,4,9,11] := remove (a 15) 1 [0,1,3,4,9,11] d15 b10
  have b11 : a 15 ≠ 3 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 3 d13 c43 (by decide +kernel)
  have t11 : a 15 ∈ [0,4,9,11] := remove (a 15) 3 [0,3,4,9,11] t10 b11
  have b12 : a 15 ≠ 4 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 4 d13 c43 (by decide +kernel)
  have t12 : a 15 ∈ [0,9,11] := remove (a 15) 4 [0,4,9,11] t11 b12
  have b13 : a 15 ≠ 9 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 9 d13 c43 (by decide +kernel)
  have t13 : a 15 ∈ [0,11] := remove (a 15) 9 [0,9,11] t12 b13
  have b14 : a 15 ≠ 11 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 11 d13 c43 (by decide +kernel)
  have t14 : a 15 ∈ [0] := remove (a 15) 11 [0,11] t13 b14
  have b15 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b15
  exact And.intro t9 (And.intro t14 (t15))

theorem chunk27 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 29 ∈ [0,1] ∧ a 31 ∈ [0,1,9,10,11] := by
  have b0 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11] d29 b0
  have b1 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,6,7,8,9,10,11] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11] t1 b2
  have b3 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,7,8,9,10,11] := remove (a 29) 6 [0,1,6,7,8,9,10,11] t2 b3
  have b4 : a 29 ≠ 7 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,8,9,10,11] := remove (a 29) 7 [0,1,7,8,9,10,11] t3 b4
  have b5 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,9,10,11] := remove (a 29) 8 [0,1,8,9,10,11] t4 b5
  have b6 : a 29 ≠ 9 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,10,11] := remove (a 29) 9 [0,1,9,10,11] t5 b6
  have b7 : a 29 ≠ 10 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,11] := remove (a 29) 10 [0,1,10,11] t6 b7
  have b8 : a 29 ≠ 11 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1] := remove (a 29) 11 [0,1,11] t7 b8
  have b9 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b9
  have b10 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 31) 4 [0,1,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,6,7,8,9,10,11] := remove (a 31) 5 [0,1,5,6,7,8,9,10,11] t11 b12
  have b13 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,7,8,9,10,11] := remove (a 31) 6 [0,1,6,7,8,9,10,11] t12 b13
  have b14 : a 31 ≠ 7 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,8,9,10,11] := remove (a 31) 7 [0,1,7,8,9,10,11] t13 b14
  have b15 : a 31 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,9,10,11] := remove (a 31) 8 [0,1,8,9,10,11] t14 b15
  exact And.intro t8 (t15)

#print axioms chunk24
#print axioms chunk25
#print axioms chunk26
#print axioms chunk27
end PartitionCover205_217
