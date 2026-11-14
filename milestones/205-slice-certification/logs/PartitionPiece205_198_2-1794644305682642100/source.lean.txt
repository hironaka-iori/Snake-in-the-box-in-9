import PartitionData205_198
namespace PartitionCover205_198
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,6,7,9,10,11])
    (d16 : a 16 ∈ [0,3])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d17 : a 17 ∈ [0,6])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d18 : a 18 ∈ [0,2])
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    : a 24 ∈ [0,1,6,7] ∧ a 21 ∈ [0,6] ∧ a 19 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 24 ≠ 9 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 9 d16 c51 (by decide +kernel)
  have t0 : a 24 ∈ [0,1,6,7,10,11] := remove (a 24) 9 [0,1,6,7,9,10,11] d24 b0
  have b1 : a 24 ≠ 10 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 10 d16 c51 (by decide +kernel)
  have t1 : a 24 ∈ [0,1,6,7,11] := remove (a 24) 10 [0,1,6,7,10,11] t0 b1
  have b2 : a 24 ≠ 11 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 11 d16 c51 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,6,7] := remove (a 24) 11 [0,1,6,7,11] t1 b2
  have b3 : a 21 ≠ 1 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t3 : a 21 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d21 b3
  have b4 : a 21 ≠ 2 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t4 : a 21 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 21) 2 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 21 ≠ 3 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 3 d17 c53 (by decide +kernel)
  have t5 : a 21 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 21) 3 [0,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 21 ≠ 4 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t6 : a 21 ∈ [0,5,6,7,8,9,10,11] := remove (a 21) 4 [0,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 21 ≠ 5 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0,6,7,8,9,10,11] := remove (a 21) 5 [0,5,6,7,8,9,10,11] t6 b7
  have b8 : a 21 ≠ 7 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 7 d17 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0,6,8,9,10,11] := remove (a 21) 7 [0,6,7,8,9,10,11] t7 b8
  have b9 : a 21 ≠ 8 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 8 d17 c53 (by decide +kernel)
  have t9 : a 21 ∈ [0,6,9,10,11] := remove (a 21) 8 [0,6,8,9,10,11] t8 b9
  have b10 : a 21 ≠ 9 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 9 d17 c53 (by decide +kernel)
  have t10 : a 21 ∈ [0,6,10,11] := remove (a 21) 9 [0,6,9,10,11] t9 b10
  have b11 : a 21 ≠ 10 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 10 d17 c53 (by decide +kernel)
  have t11 : a 21 ∈ [0,6,11] := remove (a 21) 10 [0,6,10,11] t10 b11
  have b12 : a 21 ≠ 11 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 11 d17 c53 (by decide +kernel)
  have t12 : a 21 ∈ [0,6] := remove (a 21) 11 [0,6,11] t11 b12
  have b13 : a 19 ≠ 2 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d19 b13
  have b14 : a 19 ≠ 3 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 19 ≠ 6 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 6 d18 c55 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t2 (And.intro t12 (t15))

theorem chunk9 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d18 : a 18 ∈ [0,2])
    (c55 : edge r55 (a 18) (a 19)=true)
    : a 19 ∈ [0,1,4,5,23] := by
  have b0 : a 19 ≠ 7 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d19 b0
  have b1 : a 19 ≠ 8 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 8 d18 c55 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 19 ≠ 9 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 9 d18 c55 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 19 ≠ 10 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 10 d18 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 10 [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 19 ≠ 11 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 11 d18 c55 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 11 [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 19 ≠ 12 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 12 d18 c55 (by decide +kernel)
  have t5 : a 19 ∈ [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 12 [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 19 ≠ 13 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 13 d18 c55 (by decide +kernel)
  have t6 : a 19 ∈ [0,1,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 19) 13 [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 19 ≠ 14 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 14 d18 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23] := remove (a 19) 14 [0,1,4,5,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 19 ≠ 15 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 15 d18 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := remove (a 19) 15 [0,1,4,5,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 19 ≠ 16 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 16 d18 c55 (by decide +kernel)
  have t9 : a 19 ∈ [0,1,4,5,17,18,19,20,21,22,23] := remove (a 19) 16 [0,1,4,5,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 19 ≠ 17 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 17 d18 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,1,4,5,18,19,20,21,22,23] := remove (a 19) 17 [0,1,4,5,17,18,19,20,21,22,23] t9 b10
  have b11 : a 19 ≠ 18 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 18 d18 c55 (by decide +kernel)
  have t11 : a 19 ∈ [0,1,4,5,19,20,21,22,23] := remove (a 19) 18 [0,1,4,5,18,19,20,21,22,23] t10 b11
  have b12 : a 19 ≠ 19 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 19 d18 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,4,5,20,21,22,23] := remove (a 19) 19 [0,1,4,5,19,20,21,22,23] t11 b12
  have b13 : a 19 ≠ 20 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 20 d18 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,4,5,21,22,23] := remove (a 19) 20 [0,1,4,5,20,21,22,23] t12 b13
  have b14 : a 19 ≠ 21 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 21 d18 c55 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,4,5,22,23] := remove (a 19) 21 [0,1,4,5,21,22,23] t13 b14
  have b15 : a 19 ≠ 22 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 22 d18 c55 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,4,5,23] := remove (a 19) 22 [0,1,4,5,22,23] t14 b15
  exact t15

theorem chunk10 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,4,5,23])
    (d18 : a 18 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,4,5])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c55 : edge r55 (a 18) (a 19)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    : a 19 ∈ [0,1,4,5] ∧ a 18 ∈ [0] ∧ a 26 ∈ [0,4] ∧ a 23 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := by
  have b0 : a 19 ≠ 23 := exclude [0,2] (fun u v => edge r55 v u) (a 19) (a 18) 23 d18 c55 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,4,5] := remove (a 19) 23 [0,1,4,5,23] d19 b0
  have b1 : a 18 ≠ 2 := exclude [0,1,4,5] (edge r57) (a 18) (a 26) 2 d26 c57 (by decide +kernel)
  have t1 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b1
  have b2 : a 26 ≠ 1 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 1 t1 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0,4,5] := remove (a 26) 1 [0,1,4,5] d26 b2
  have b3 : a 26 ≠ 5 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 5 t1 c57 (by decide +kernel)
  have t3 : a 26 ∈ [0,4] := remove (a 26) 5 [0,4,5] t2 b3
  have b4 : a 23 ≠ 2 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 2 t0 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d23 b4
  have b5 : a 23 ≠ 3 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 3 t0 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 23 ≠ 6 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 6 t0 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 23 ≠ 7 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 7 t0 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 23 ≠ 8 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 8 t0 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 23 ≠ 9 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 9 t0 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 23 ≠ 10 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 10 t0 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 10 [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 23 ≠ 11 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 11 t0 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 11 [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 23 ≠ 12 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 12 t0 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 12 [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 23 ≠ 13 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 13 t0 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 23) 13 [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 23 ≠ 14 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 14 t0 c58 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23] := remove (a 23) 14 [0,1,4,5,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 23 ≠ 15 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 15 t0 c58 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := remove (a 23) 15 [0,1,4,5,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (t15)))

theorem chunk11 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,4,5,16,17,18,19,20,21,22,23])
    (d19 : a 19 ∈ [0,1,4,5])
    (d20 : a 20 ∈ [0,1])
    (d21 : a 21 ∈ [0,6])
    (d28 : a 28 ∈ [0,2,3])
    (d29 : a 29 ∈ [0,1,6,7])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d22 : a 22 ∈ [0,3])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 23 ∈ [0,1,4,5] ∧ a 20 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0,6] ∧ a 30 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 23 ≠ 16 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 16 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,4,5,17,18,19,20,21,22,23] := remove (a 23) 16 [0,1,4,5,16,17,18,19,20,21,22,23] d23 b0
  have b1 : a 23 ≠ 17 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 17 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,4,5,18,19,20,21,22,23] := remove (a 23) 17 [0,1,4,5,17,18,19,20,21,22,23] t0 b1
  have b2 : a 23 ≠ 18 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 18 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,1,4,5,19,20,21,22,23] := remove (a 23) 18 [0,1,4,5,18,19,20,21,22,23] t1 b2
  have b3 : a 23 ≠ 19 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 19 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,4,5,20,21,22,23] := remove (a 23) 19 [0,1,4,5,19,20,21,22,23] t2 b3
  have b4 : a 23 ≠ 20 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 20 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,4,5,21,22,23] := remove (a 23) 20 [0,1,4,5,20,21,22,23] t3 b4
  have b5 : a 23 ≠ 21 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 21 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,4,5,22,23] := remove (a 23) 21 [0,1,4,5,21,22,23] t4 b5
  have b6 : a 23 ≠ 22 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 22 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,4,5,23] := remove (a 23) 22 [0,1,4,5,22,23] t5 b6
  have b7 : a 23 ≠ 23 := exclude [0,1,4,5] (fun u v => edge r58 v u) (a 23) (a 19) 23 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,4,5] := remove (a 23) 23 [0,1,4,5,23] t6 b7
  have b8 : a 20 ≠ 1 := exclude [0,6] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b8
  have b9 : a 28 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 2 t8 c62 (by decide +kernel)
  have t9 : a 28 ∈ [0,3] := remove (a 28) 2 [0,2,3] d28 b9
  have b10 : a 28 ≠ 3 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 3 t8 c62 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 3 [0,3] t9 b10
  have b11 : a 29 ≠ 1 := exclude [0,6] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0,6,7] := remove (a 29) 1 [0,1,6,7] d29 b11
  have b12 : a 29 ≠ 7 := exclude [0,6] (fun u v => edge r64 v u) (a 29) (a 21) 7 d21 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,6] := remove (a 29) 7 [0,6,7] t11 b12
  have b13 : a 30 ≠ 1 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d30 b13
  have b14 : a 30 ≠ 3 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 3 d22 c66 (by decide +kernel)
  have t14 : a 30 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 30 ≠ 5 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 5 d22 c66 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 5 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (t15))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_198
