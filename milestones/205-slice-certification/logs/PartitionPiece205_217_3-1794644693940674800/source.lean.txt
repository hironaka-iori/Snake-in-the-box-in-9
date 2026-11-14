import PartitionData205_217
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d4 : a 4 ∈ [0,6])
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 20 ∈ [0,1,2,3,4,5,22,23] := by
  have b0 : a 20 ≠ 6 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d20 b0
  have b1 : a 20 ≠ 7 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 20 ≠ 8 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 20 ≠ 9 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 20 ≠ 10 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 20 ≠ 11 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 20 ≠ 12 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 12 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 12 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 20 ≠ 13 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 13 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 13 [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 20 ≠ 14 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 14 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] := remove (a 20) 14 [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 20 ≠ 15 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 15 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,2,3,4,5,16,17,18,19,20,21,22,23] := remove (a 20) 15 [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 20 ≠ 16 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 16 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := remove (a 20) 16 [0,1,2,3,4,5,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 20 ≠ 17 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 17 d4 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := remove (a 20) 17 [0,1,2,3,4,5,17,18,19,20,21,22,23] t10 b11
  have b12 : a 20 ≠ 18 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 18 d4 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,2,3,4,5,19,20,21,22,23] := remove (a 20) 18 [0,1,2,3,4,5,18,19,20,21,22,23] t11 b12
  have b13 : a 20 ≠ 19 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 19 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,2,3,4,5,20,21,22,23] := remove (a 20) 19 [0,1,2,3,4,5,19,20,21,22,23] t12 b13
  have b14 : a 20 ≠ 20 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 20 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,2,3,4,5,21,22,23] := remove (a 20) 20 [0,1,2,3,4,5,20,21,22,23] t13 b14
  have b15 : a 20 ≠ 21 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 21 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,2,3,4,5,22,23] := remove (a 20) 21 [0,1,2,3,4,5,21,22,23] t14 b15
  exact t15

theorem chunk13 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,2,3,4,5,22,23])
    (d4 : a 4 ∈ [0,6])
    (d5 : a 5 ∈ [0,2,12,14])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 20 ∈ [0,1,2,3,4,5] ∧ a 5 ∈ [0,2] ∧ a 7 ∈ [0,2] ∧ a 13 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 20 ≠ 22 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 22 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,2,3,4,5,23] := remove (a 20) 22 [0,1,2,3,4,5,22,23] d20 b0
  have b1 : a 20 ≠ 23 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 23 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,2,3,4,5] := remove (a 20) 23 [0,1,2,3,4,5,23] t0 b1
  have b2 : a 5 ≠ 12 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r20) (a 5) (a 7) 12 d7 c20 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,14] := remove (a 5) 12 [0,2,12,14] d5 b2
  have b3 : a 5 ≠ 14 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r20) (a 5) (a 7) 14 d7 c20 (by decide +kernel)
  have t3 : a 5 ∈ [0,2] := remove (a 5) 14 [0,2,14] t2 b3
  have b4 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 1 t3 c20 (by decide +kernel)
  have t4 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d7 b4
  have b5 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 3 t3 c20 (by decide +kernel)
  have t5 : a 7 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 7) 3 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 7 ≠ 4 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 4 t3 c20 (by decide +kernel)
  have t6 : a 7 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 7) 4 [0,2,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 7 ≠ 5 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 5 t3 c20 (by decide +kernel)
  have t7 : a 7 ∈ [0,2,6,7,8,9,10,11] := remove (a 7) 5 [0,2,5,6,7,8,9,10,11] t6 b7
  have b8 : a 7 ≠ 6 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 6 t3 c20 (by decide +kernel)
  have t8 : a 7 ∈ [0,2,7,8,9,10,11] := remove (a 7) 6 [0,2,6,7,8,9,10,11] t7 b8
  have b9 : a 7 ≠ 7 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 7 t3 c20 (by decide +kernel)
  have t9 : a 7 ∈ [0,2,8,9,10,11] := remove (a 7) 7 [0,2,7,8,9,10,11] t8 b9
  have b10 : a 7 ≠ 8 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 8 t3 c20 (by decide +kernel)
  have t10 : a 7 ∈ [0,2,9,10,11] := remove (a 7) 8 [0,2,8,9,10,11] t9 b10
  have b11 : a 7 ≠ 9 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 9 t3 c20 (by decide +kernel)
  have t11 : a 7 ∈ [0,2,10,11] := remove (a 7) 9 [0,2,9,10,11] t10 b11
  have b12 : a 7 ≠ 10 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 10 t3 c20 (by decide +kernel)
  have t12 : a 7 ∈ [0,2,11] := remove (a 7) 10 [0,2,10,11] t11 b12
  have b13 : a 7 ≠ 11 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 11 t3 c20 (by decide +kernel)
  have t13 : a 7 ∈ [0,2] := remove (a 7) 11 [0,2,11] t12 b13
  have b14 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 1 t3 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d13 b14
  have b15 : a 13 ≠ 2 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 2 t3 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t13 (t15)))

theorem chunk14 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d5 : a 5 ∈ [0,2])
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 13 ∈ [0,12,20,21,22,23] := by
  have b0 : a 13 ≠ 3 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d13 b0
  have b1 : a 13 ≠ 4 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 13 ≠ 5 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 13 ≠ 6 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 13 ≠ 7 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 13 ≠ 8 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 13 ≠ 9 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 9 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 13 ≠ 10 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 10 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 13 ≠ 11 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 11 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 13 ≠ 13 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 13 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,12,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 13 [0,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 13 ≠ 14 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 14 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,12,15,16,17,18,19,20,21,22,23] := remove (a 13) 14 [0,12,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 13 ≠ 15 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 15 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,12,16,17,18,19,20,21,22,23] := remove (a 13) 15 [0,12,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 13 ≠ 16 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 16 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,12,17,18,19,20,21,22,23] := remove (a 13) 16 [0,12,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 13 ≠ 17 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 17 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,12,18,19,20,21,22,23] := remove (a 13) 17 [0,12,17,18,19,20,21,22,23] t12 b13
  have b14 : a 13 ≠ 18 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 18 d5 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,12,19,20,21,22,23] := remove (a 13) 18 [0,12,18,19,20,21,22,23] t13 b14
  have b15 : a 13 ≠ 19 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 19 d5 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,12,20,21,22,23] := remove (a 13) 19 [0,12,19,20,21,22,23] t14 b15
  exact t15

theorem chunk15 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,12,20,21,22,23])
    (d5 : a 5 ∈ [0,2])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 13 ∈ [0,12] ∧ a 21 ∈ [0,8,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 13 ≠ 20 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 20 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,12,21,22,23] := remove (a 13) 20 [0,12,20,21,22,23] d13 b0
  have b1 : a 13 ≠ 21 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 21 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,12,22,23] := remove (a 13) 21 [0,12,21,22,23] t0 b1
  have b2 : a 13 ≠ 22 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 22 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,12,23] := remove (a 13) 22 [0,12,22,23] t1 b2
  have b3 : a 13 ≠ 23 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 23 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,12] := remove (a 13) 23 [0,12,23] t2 b3
  have b4 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d21 b4
  have b5 : a 21 ≠ 2 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 21 ≠ 4 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 21 ≠ 5 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 21 ≠ 6 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 6 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 21 ≠ 7 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 21 ≠ 9 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 9 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 9 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 21 ≠ 10 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 10 d5 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 10 [0,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 21 ≠ 11 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 11 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 11 [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 21 ≠ 12 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 12 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,8,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 12 [0,8,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 21 ≠ 13 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 13 d5 c22 (by decide +kernel)
  have t15 : a 21 ∈ [0,8,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 13 [0,8,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (t15)

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_217
