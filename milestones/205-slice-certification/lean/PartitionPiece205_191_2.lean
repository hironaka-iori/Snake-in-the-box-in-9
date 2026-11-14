import PartitionData205_191
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d8 : a 8 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,4,5])
    (d11 : a 11 ∈ [0,1,2,3,4,7,8])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 24 ∈ [0,4,5,16] ∧ a 9 ∈ [0,5] ∧ a 11 ∈ [0,2,3,4,7,8] := by
  have b0 : a 24 ≠ 10 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 10 [0,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b0
  have b1 : a 24 ≠ 11 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 11 [0,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 24 ≠ 12 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 12 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 12 [0,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 24 ≠ 13 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 13 [0,4,5,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 24 ≠ 14 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 14 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,4,5,15,16,17,18,19,20,21,22,23] := remove (a 24) 14 [0,4,5,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 24 ≠ 15 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,4,5,16,17,18,19,20,21,22,23] := remove (a 24) 15 [0,4,5,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 24 ≠ 17 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,4,5,16,18,19,20,21,22,23] := remove (a 24) 17 [0,4,5,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 24 ≠ 18 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 18 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,4,5,16,19,20,21,22,23] := remove (a 24) 18 [0,4,5,16,18,19,20,21,22,23] t6 b7
  have b8 : a 24 ≠ 19 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 19 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,4,5,16,20,21,22,23] := remove (a 24) 19 [0,4,5,16,19,20,21,22,23] t7 b8
  have b9 : a 24 ≠ 20 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 20 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,4,5,16,21,22,23] := remove (a 24) 20 [0,4,5,16,20,21,22,23] t8 b9
  have b10 : a 24 ≠ 21 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 21 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,4,5,16,22,23] := remove (a 24) 21 [0,4,5,16,21,22,23] t9 b10
  have b11 : a 24 ≠ 22 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 22 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,4,5,16,23] := remove (a 24) 22 [0,4,5,16,22,23] t10 b11
  have b12 : a 24 ≠ 23 := exclude [0,1,2,3] (fun u v => edge r31 v u) (a 24) (a 8) 23 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,4,5,16] := remove (a 24) 23 [0,4,5,16,23] t11 b12
  have b13 : a 9 ≠ 1 := exclude [0,1,2,3,4,7,8] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t13 : a 9 ∈ [0,4,5] := remove (a 9) 1 [0,1,4,5] d9 b13
  have b14 : a 9 ≠ 4 := exclude [0,1,2,3,4,7,8] (edge r32) (a 9) (a 11) 4 d11 c32 (by decide +kernel)
  have t14 : a 9 ∈ [0,5] := remove (a 9) 4 [0,4,5] t13 b14
  have b15 : a 11 ≠ 1 := exclude [0,5] (fun u v => edge r32 v u) (a 11) (a 9) 1 t14 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,3,4,7,8] := remove (a 11) 1 [0,1,2,3,4,7,8] d11 b15
  exact And.intro t12 (And.intro t14 (t15))

theorem chunk9 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,3,4,7,8])
    (d9 : a 9 ∈ [0,5])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 11 ∈ [0,4] ∧ a 25 ∈ [0,1,3,4,6,7,8,17,18,19,21,23] := by
  have b0 : a 11 ≠ 2 := exclude [0,5] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t0 : a 11 ∈ [0,3,4,7,8] := remove (a 11) 2 [0,2,3,4,7,8] d11 b0
  have b1 : a 11 ≠ 3 := exclude [0,5] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t1 : a 11 ∈ [0,4,7,8] := remove (a 11) 3 [0,3,4,7,8] t0 b1
  have b2 : a 11 ≠ 7 := exclude [0,5] (fun u v => edge r32 v u) (a 11) (a 9) 7 d9 c32 (by decide +kernel)
  have t2 : a 11 ∈ [0,4,8] := remove (a 11) 7 [0,4,7,8] t1 b2
  have b3 : a 11 ≠ 8 := exclude [0,5] (fun u v => edge r32 v u) (a 11) (a 9) 8 d9 c32 (by decide +kernel)
  have t3 : a 11 ∈ [0,4] := remove (a 11) 8 [0,4,8] t2 b3
  have b4 : a 25 ≠ 2 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d25 b4
  have b5 : a 25 ≠ 5 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 5 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 25 ≠ 9 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,3,4,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 9 [0,1,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 25 ≠ 10 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,3,4,6,7,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 10 [0,1,3,4,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 25 ≠ 11 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,3,4,6,7,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 11 [0,1,3,4,6,7,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 25 ≠ 12 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,3,4,6,7,8,13,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 12 [0,1,3,4,6,7,8,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 25 ≠ 13 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,3,4,6,7,8,14,15,16,17,18,19,20,21,22,23] := remove (a 25) 13 [0,1,3,4,6,7,8,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 25 ≠ 14 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 14 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,3,4,6,7,8,15,16,17,18,19,20,21,22,23] := remove (a 25) 14 [0,1,3,4,6,7,8,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 25 ≠ 15 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 15 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,3,4,6,7,8,16,17,18,19,20,21,22,23] := remove (a 25) 15 [0,1,3,4,6,7,8,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 25 ≠ 16 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,3,4,6,7,8,17,18,19,20,21,22,23] := remove (a 25) 16 [0,1,3,4,6,7,8,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 25 ≠ 20 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 20 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,3,4,6,7,8,17,18,19,21,22,23] := remove (a 25) 20 [0,1,3,4,6,7,8,17,18,19,20,21,22,23] t13 b14
  have b15 : a 25 ≠ 22 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 22 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,3,4,6,7,8,17,18,19,21,23] := remove (a 25) 22 [0,1,3,4,6,7,8,17,18,19,21,22,23] t14 b15
  exact And.intro t3 (t15)

theorem chunk10 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,5,7,23])
    (d11 : a 11 ∈ [0,4])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 10 ∈ [0,5] ∧ a 26 ∈ [0,1,2,12,18,19,20,21,22,23] := by
  have b0 : a 10 ≠ 7 := exclude [0,4] (edge r35) (a 10) (a 11) 7 d11 c35 (by decide +kernel)
  have t0 : a 10 ∈ [0,5,23] := remove (a 10) 7 [0,5,7,23] d10 b0
  have b1 : a 10 ≠ 23 := exclude [0,4] (edge r35) (a 10) (a 11) 23 d11 c35 (by decide +kernel)
  have t1 : a 10 ∈ [0,5] := remove (a 10) 23 [0,5,23] t0 b1
  have b2 : a 26 ≠ 3 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 3 t1 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 3 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b2
  have b3 : a 26 ≠ 4 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 4 t1 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 4 [0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 26 ≠ 5 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 5 t1 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,1,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 26 ≠ 6 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 6 t1 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 6 [0,1,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 26 ≠ 7 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 7 t1 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 7 [0,1,2,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 26 ≠ 8 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 8 t1 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 8 [0,1,2,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 26 ≠ 9 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 9 t1 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 9 [0,1,2,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 26 ≠ 10 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 10 t1 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 10 [0,1,2,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 11 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 11 t1 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,2,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 11 [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 26 ≠ 13 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 13 t1 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,2,12,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 13 [0,1,2,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 26 ≠ 14 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 14 t1 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,2,12,15,16,17,18,19,20,21,22,23] := remove (a 26) 14 [0,1,2,12,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 26 ≠ 15 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 15 t1 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,2,12,16,17,18,19,20,21,22,23] := remove (a 26) 15 [0,1,2,12,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 26 ≠ 16 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 16 t1 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,2,12,17,18,19,20,21,22,23] := remove (a 26) 16 [0,1,2,12,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 26 ≠ 17 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 17 t1 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,2,12,18,19,20,21,22,23] := remove (a 26) 17 [0,1,2,12,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (t15)

theorem chunk11 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,2,12,18,19,20,21,22,23])
    (d10 : a 10 ∈ [0,5])
    (d15 : a 15 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23])
    (d11 : a 11 ∈ [0,4])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 26 ∈ [0,1,2,12] ∧ a 15 ∈ [0,10,13,19,20,21,22,23] := by
  have b0 : a 26 ≠ 18 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 18 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,2,12,19,20,21,22,23] := remove (a 26) 18 [0,1,2,12,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 19 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 19 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,2,12,20,21,22,23] := remove (a 26) 19 [0,1,2,12,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 20 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 20 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,2,12,21,22,23] := remove (a 26) 20 [0,1,2,12,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 21 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 21 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,2,12,22,23] := remove (a 26) 21 [0,1,2,12,21,22,23] t2 b3
  have b4 : a 26 ≠ 22 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 22 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,2,12,23] := remove (a 26) 22 [0,1,2,12,22,23] t3 b4
  have b5 : a 26 ≠ 23 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 23 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,2,12] := remove (a 26) 23 [0,1,2,12,23] t4 b5
  have b6 : a 15 ≠ 1 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,2,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23] := remove (a 15) 1 [0,1,2,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23] d15 b6
  have b7 : a 15 ≠ 2 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23] := remove (a 15) 2 [0,2,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23] t6 b7
  have b8 : a 15 ≠ 3 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0,4,5,10,11,12,13,14,15,18,19,20,21,22,23] := remove (a 15) 3 [0,3,4,5,10,11,12,13,14,15,18,19,20,21,22,23] t7 b8
  have b9 : a 15 ≠ 4 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0,5,10,11,12,13,14,15,18,19,20,21,22,23] := remove (a 15) 4 [0,4,5,10,11,12,13,14,15,18,19,20,21,22,23] t8 b9
  have b10 : a 15 ≠ 5 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0,10,11,12,13,14,15,18,19,20,21,22,23] := remove (a 15) 5 [0,5,10,11,12,13,14,15,18,19,20,21,22,23] t9 b10
  have b11 : a 15 ≠ 11 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 11 d11 c38 (by decide +kernel)
  have t11 : a 15 ∈ [0,10,12,13,14,15,18,19,20,21,22,23] := remove (a 15) 11 [0,10,11,12,13,14,15,18,19,20,21,22,23] t10 b11
  have b12 : a 15 ≠ 12 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 12 d11 c38 (by decide +kernel)
  have t12 : a 15 ∈ [0,10,13,14,15,18,19,20,21,22,23] := remove (a 15) 12 [0,10,12,13,14,15,18,19,20,21,22,23] t11 b12
  have b13 : a 15 ≠ 14 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 14 d11 c38 (by decide +kernel)
  have t13 : a 15 ∈ [0,10,13,15,18,19,20,21,22,23] := remove (a 15) 14 [0,10,13,14,15,18,19,20,21,22,23] t12 b13
  have b14 : a 15 ≠ 15 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 15 d11 c38 (by decide +kernel)
  have t14 : a 15 ∈ [0,10,13,18,19,20,21,22,23] := remove (a 15) 15 [0,10,13,15,18,19,20,21,22,23] t13 b14
  have b15 : a 15 ≠ 18 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 18 d11 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0,10,13,19,20,21,22,23] := remove (a 15) 18 [0,10,13,18,19,20,21,22,23] t14 b15
  exact And.intro t5 (t15)

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_191
