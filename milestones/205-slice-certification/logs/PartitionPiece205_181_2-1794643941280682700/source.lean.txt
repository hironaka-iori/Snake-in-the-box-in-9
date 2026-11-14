import PartitionData205_181
namespace PartitionCover205_181
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,2,3,12,13,14,15])
    (d11 : a 11 ∈ [0,6])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d13 : a 13 ∈ [0,1,3,5])
    (d12 : a 12 ∈ [0,2])
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    : a 15 ∈ [0,12,15] ∧ a 27 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 15 ≠ 13 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 13 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [0,2,3,12,14,15] := remove (a 15) 13 [0,2,3,12,13,14,15] d15 b0
  have b1 : a 27 ≠ 1 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9] d27 b1
  have b2 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,3,4,5,6,7,8,9] := remove (a 27) 2 [0,2,3,4,5,6,7,8,9] t1 b2
  have b3 : a 27 ≠ 3 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,4,5,6,7,8,9] := remove (a 27) 3 [0,3,4,5,6,7,8,9] t2 b3
  have b4 : a 27 ≠ 4 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,5,6,7,8,9] := remove (a 27) 4 [0,4,5,6,7,8,9] t3 b4
  have b5 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,6,7,8,9] := remove (a 27) 5 [0,5,6,7,8,9] t4 b5
  have b6 : a 27 ≠ 6 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,7,8,9] := remove (a 27) 6 [0,6,7,8,9] t5 b6
  have b7 : a 27 ≠ 7 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,8,9] := remove (a 27) 7 [0,7,8,9] t6 b7
  have b8 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,9] := remove (a 27) 8 [0,8,9] t7 b8
  have b9 : a 27 ≠ 9 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0] := remove (a 27) 9 [0,9] t8 b9
  have b10 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r40 v u) (a 13) (a 12) 1 d12 c40 (by decide +kernel)
  have t10 : a 13 ∈ [0,3,5] := remove (a 13) 1 [0,1,3,5] d13 b10
  have b11 : a 13 ≠ 3 := exclude [0,2] (fun u v => edge r40 v u) (a 13) (a 12) 3 d12 c40 (by decide +kernel)
  have t11 : a 13 ∈ [0,5] := remove (a 13) 3 [0,3,5] t10 b11
  have b12 : a 13 ≠ 5 := exclude [0,2] (fun u v => edge r40 v u) (a 13) (a 12) 5 d12 c40 (by decide +kernel)
  have t12 : a 13 ∈ [0] := remove (a 13) 5 [0,5] t11 b12
  have b13 : a 15 ≠ 2 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 2 t12 c43 (by decide +kernel)
  have t13 : a 15 ∈ [0,3,12,14,15] := remove (a 15) 2 [0,2,3,12,14,15] t0 b13
  have b14 : a 15 ≠ 3 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 3 t12 c43 (by decide +kernel)
  have t14 : a 15 ∈ [0,12,14,15] := remove (a 15) 3 [0,3,12,14,15] t13 b14
  have b15 : a 15 ≠ 14 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 14 t12 c43 (by decide +kernel)
  have t15 : a 15 ∈ [0,12,15] := remove (a 15) 14 [0,12,14,15] t14 b15
  exact And.intro t15 (And.intro t9 (t12))

theorem chunk9 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,12,15])
    (d13 : a 13 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 15 ∈ [0,12] ∧ a 29 ∈ [0,2,17,18,19,20,21,22,23] := by
  have b0 : a 15 ≠ 15 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 15 d13 c43 (by decide +kernel)
  have t0 : a 15 ∈ [0,12] := remove (a 15) 15 [0,12,15] d15 b0
  have b1 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b1
  have b2 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 7 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 9 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 10 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 10 [0,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 11 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 11 [0,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 12 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,2,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,2,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 13 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,2,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,2,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 14 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,2,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 15 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,2,16,17,18,19,20,21,22,23] := remove (a 29) 15 [0,2,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 16 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,17,18,19,20,21,22,23] := remove (a 29) 16 [0,2,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (t15)

theorem chunk10 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d14 : a 14 ∈ [0,4])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,2] ∧ a 30 ∈ [0,1,2,6,7,8,15,16,17] := by
  have b0 : a 29 ≠ 17 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,18,19,20,21,22,23] := remove (a 29) 17 [0,2,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 18 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,2,19,20,21,22,23] := remove (a 29) 18 [0,2,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 19 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,2,20,21,22,23] := remove (a 29) 19 [0,2,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 20 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,2,21,22,23] := remove (a 29) 20 [0,2,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 21 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 21 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,2,22,23] := remove (a 29) 21 [0,2,21,22,23] t3 b4
  have b5 : a 29 ≠ 22 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,2,23] := remove (a 29) 22 [0,2,22,23] t4 b5
  have b6 : a 29 ≠ 23 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,2] := remove (a 29) 23 [0,2,23] t5 b6
  have b7 : a 30 ≠ 3 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d30 b7
  have b8 : a 30 ≠ 4 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 4 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 30 ≠ 5 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 5 [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 30 ≠ 9 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,2,6,7,8,10,11,12,13,14,15,16,17] := remove (a 30) 9 [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 30 ≠ 10 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,2,6,7,8,11,12,13,14,15,16,17] := remove (a 30) 10 [0,1,2,6,7,8,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 30 ≠ 11 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,2,6,7,8,12,13,14,15,16,17] := remove (a 30) 11 [0,1,2,6,7,8,11,12,13,14,15,16,17] t11 b12
  have b13 : a 30 ≠ 12 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,2,6,7,8,13,14,15,16,17] := remove (a 30) 12 [0,1,2,6,7,8,12,13,14,15,16,17] t12 b13
  have b14 : a 30 ≠ 13 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,2,6,7,8,14,15,16,17] := remove (a 30) 13 [0,1,2,6,7,8,13,14,15,16,17] t13 b14
  have b15 : a 30 ≠ 14 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,2,6,7,8,15,16,17] := remove (a 30) 14 [0,1,2,6,7,8,14,15,16,17] t14 b15
  exact And.intro t6 (t15)

theorem chunk11 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,6,7,8,15,16,17])
    (d14 : a 14 ∈ [0,4])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,12])
    (d21 : a 21 ∈ [0,1,3,5])
    (d17 : a 17 ∈ [0,1])
    (d25 : a 25 ∈ [0,2,3,4,7,8])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    : a 30 ∈ [0,1,2,6,7,8] ∧ a 31 ∈ [0,1,2,3,5,7,11,12,13,14,15,16,17,21,22,23] ∧ a 21 ∈ [0,1] ∧ a 25 ∈ [0,4,8] := by
  have b0 : a 30 ≠ 15 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,2,6,7,8,16,17] := remove (a 30) 15 [0,1,2,6,7,8,15,16,17] d30 b0
  have b1 : a 30 ≠ 16 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,2,6,7,8,17] := remove (a 30) 16 [0,1,2,6,7,8,16,17] t0 b1
  have b2 : a 30 ≠ 17 := exclude [0,4] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,2,6,7,8] := remove (a 30) 17 [0,1,2,6,7,8,17] t1 b2
  have b3 : a 31 ≠ 4 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b3
  have b4 : a 31 ≠ 6 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,2,3,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 6 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 31 ≠ 8 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,2,3,5,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 8 [0,1,2,3,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 31 ≠ 9 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,2,3,5,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 9 [0,1,2,3,5,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 31 ≠ 10 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,2,3,5,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 10 [0,1,2,3,5,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 31 ≠ 18 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 18 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,2,3,5,7,11,12,13,14,15,16,17,19,20,21,22,23] := remove (a 31) 18 [0,1,2,3,5,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 31 ≠ 19 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 19 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,2,3,5,7,11,12,13,14,15,16,17,20,21,22,23] := remove (a 31) 19 [0,1,2,3,5,7,11,12,13,14,15,16,17,19,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 20 := exclude [0,12] (fun u v => edge r47 v u) (a 31) (a 15) 20 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,2,3,5,7,11,12,13,14,15,16,17,21,22,23] := remove (a 31) 20 [0,1,2,3,5,7,11,12,13,14,15,16,17,20,21,22,23] t9 b10
  have b11 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 3 d17 c53 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,5] := remove (a 21) 3 [0,1,3,5] d21 b11
  have b12 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t12 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t11 b12
  have b13 : a 25 ≠ 2 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 2 d17 c54 (by decide +kernel)
  have t13 : a 25 ∈ [0,3,4,7,8] := remove (a 25) 2 [0,2,3,4,7,8] d25 b13
  have b14 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 3 d17 c54 (by decide +kernel)
  have t14 : a 25 ∈ [0,4,7,8] := remove (a 25) 3 [0,3,4,7,8] t13 b14
  have b15 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 7 d17 c54 (by decide +kernel)
  have t15 : a 25 ∈ [0,4,8] := remove (a 25) 7 [0,4,7,8] t14 b15
  exact And.intro t2 (And.intro t10 (And.intro t12 (t15)))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_181
