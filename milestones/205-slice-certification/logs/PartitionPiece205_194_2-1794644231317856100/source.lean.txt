import PartitionData205_194
namespace PartitionCover205_194
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d18 : a 18 ∈ [0])
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 26 ∈ [0,1,2,3,12,13] := by
  have b0 : a 26 ≠ 6 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 6 d18 c57 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 7 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 7 d18 c57 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 8 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 8 d18 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 9 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 9 d18 c57 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 26 ≠ 10 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 10 d18 c57 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 26 ≠ 11 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 11 d18 c57 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 26 ≠ 14 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 14 d18 c57 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,2,3,12,13,15,16,17,18,19,20,21,22,23] := remove (a 26) 14 [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 26 ≠ 15 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 15 d18 c57 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,2,3,12,13,16,17,18,19,20,21,22,23] := remove (a 26) 15 [0,1,2,3,12,13,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 26 ≠ 16 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 16 d18 c57 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,2,3,12,13,17,18,19,20,21,22,23] := remove (a 26) 16 [0,1,2,3,12,13,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 26 ≠ 17 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 17 d18 c57 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,2,3,12,13,18,19,20,21,22,23] := remove (a 26) 17 [0,1,2,3,12,13,17,18,19,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 18 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 18 d18 c57 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,2,3,12,13,19,20,21,22,23] := remove (a 26) 18 [0,1,2,3,12,13,18,19,20,21,22,23] t9 b10
  have b11 : a 26 ≠ 19 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 19 d18 c57 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,2,3,12,13,20,21,22,23] := remove (a 26) 19 [0,1,2,3,12,13,19,20,21,22,23] t10 b11
  have b12 : a 26 ≠ 20 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 20 d18 c57 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,2,3,12,13,21,22,23] := remove (a 26) 20 [0,1,2,3,12,13,20,21,22,23] t11 b12
  have b13 : a 26 ≠ 21 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 21 d18 c57 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,2,3,12,13,22,23] := remove (a 26) 21 [0,1,2,3,12,13,21,22,23] t12 b13
  have b14 : a 26 ≠ 22 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 22 d18 c57 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,2,3,12,13,23] := remove (a 26) 22 [0,1,2,3,12,13,22,23] t13 b14
  have b15 : a 26 ≠ 23 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 23 d18 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,2,3,12,13] := remove (a 26) 23 [0,1,2,3,12,13,23] t14 b15
  exact t15

theorem chunk9 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d19 : a 19 ∈ [0])
    (d21 : a 21 ∈ [0,4])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 23 ∈ [0,6] := by
  have b0 : a 23 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d23 b0
  have b1 : a 23 ≠ 2 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 23) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 23 ≠ 3 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 23) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 23 ≠ 4 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 23) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 23 ≠ 7 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,5,6,8,9,10,11,12,13,14,15,16,17] := remove (a 23) 7 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 23 ≠ 8 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 8 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,5,6,9,10,11,12,13,14,15,16,17] := remove (a 23) 8 [0,5,6,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 23 ≠ 9 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 9 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,5,6,10,11,12,13,14,15,16,17] := remove (a 23) 9 [0,5,6,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 23 ≠ 10 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 10 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,5,6,11,12,13,14,15,16,17] := remove (a 23) 10 [0,5,6,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 23 ≠ 12 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 12 d19 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,5,6,11,13,14,15,16,17] := remove (a 23) 12 [0,5,6,11,12,13,14,15,16,17] t7 b8
  have b9 : a 23 ≠ 13 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 13 d19 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,5,6,11,14,15,16,17] := remove (a 23) 13 [0,5,6,11,13,14,15,16,17] t8 b9
  have b10 : a 23 ≠ 14 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 14 d19 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,5,6,11,15,16,17] := remove (a 23) 14 [0,5,6,11,14,15,16,17] t9 b10
  have b11 : a 23 ≠ 15 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 15 d19 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,5,6,11,16,17] := remove (a 23) 15 [0,5,6,11,15,16,17] t10 b11
  have b12 : a 23 ≠ 16 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 16 d19 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,5,6,11,17] := remove (a 23) 16 [0,5,6,11,16,17] t11 b12
  have b13 : a 23 ≠ 17 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 17 d19 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,5,6,11] := remove (a 23) 17 [0,5,6,11,17] t12 b13
  have b14 : a 23 ≠ 5 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 5 d21 c63 (by decide +kernel)
  have t14 : a 23 ∈ [0,6,11] := remove (a 23) 5 [0,5,6,11] t13 b14
  have b15 : a 23 ≠ 11 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 11 d21 c63 (by decide +kernel)
  have t15 : a 23 ∈ [0,6] := remove (a 23) 11 [0,6,11] t14 b15
  exact t15

theorem chunk10 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,3])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (d23 : a 23 ∈ [0,6])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d24 : a 24 ∈ [0,2])
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 30 ∈ [0,1,3,4] ∧ a 31 ∈ [0,3] ∧ a 25 ∈ [0,2,6,8,14,15,16,17] := by
  have b0 : a 30 ≠ 2 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 2 d22 c66 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,3,4,5] := remove (a 30) 2 [0,1,2,3,4,5] d30 b0
  have b1 : a 30 ≠ 5 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 5 d22 c66 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,3,4] := remove (a 30) 5 [0,1,3,4,5] t0 b1
  have b2 : a 31 ≠ 1 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 1 d23 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0,2,3,4,5] := remove (a 31) 1 [0,1,2,3,4,5] d31 b2
  have b3 : a 31 ≠ 2 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,3,4,5] := remove (a 31) 2 [0,2,3,4,5] t2 b3
  have b4 : a 31 ≠ 4 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 4 d23 c67 (by decide +kernel)
  have t4 : a 31 ∈ [0,3,5] := remove (a 31) 4 [0,3,4,5] t3 b4
  have b5 : a 31 ≠ 5 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t5 : a 31 ∈ [0,3] := remove (a 31) 5 [0,3,5] t4 b5
  have b6 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d25 b6
  have b7 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 3 d24 c68 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 25 ≠ 4 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 5 d24 c68 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 7 d24 c68 (by decide +kernel)
  have t10 : a 25 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 7 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 25 ≠ 9 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 9 d24 c68 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,6,8,10,11,12,13,14,15,16,17] := remove (a 25) 9 [0,2,6,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 25 ≠ 10 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 10 d24 c68 (by decide +kernel)
  have t12 : a 25 ∈ [0,2,6,8,11,12,13,14,15,16,17] := remove (a 25) 10 [0,2,6,8,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 11 d24 c68 (by decide +kernel)
  have t13 : a 25 ∈ [0,2,6,8,12,13,14,15,16,17] := remove (a 25) 11 [0,2,6,8,11,12,13,14,15,16,17] t12 b13
  have b14 : a 25 ≠ 12 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 12 d24 c68 (by decide +kernel)
  have t14 : a 25 ∈ [0,2,6,8,13,14,15,16,17] := remove (a 25) 12 [0,2,6,8,12,13,14,15,16,17] t13 b14
  have b15 : a 25 ≠ 13 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 13 d24 c68 (by decide +kernel)
  have t15 : a 25 ∈ [0,2,6,8,14,15,16,17] := remove (a 25) 13 [0,2,6,8,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t5 (t15))

theorem chunk11 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,2,6,8,14,15,16,17])
    (d24 : a 24 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3,12,13])
    (d28 : a 28 ∈ [0,2,6,8])
    (d29 : a 29 ∈ [0,1,6,7,12,13])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 25 ∈ [0,6] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0,1] ∧ a 28 ∈ [0,6] ∧ a 29 ∈ [0,6,13] := by
  have b0 : a 25 ≠ 14 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 14 d24 c68 (by decide +kernel)
  have t0 : a 25 ∈ [0,2,6,8,15,16,17] := remove (a 25) 14 [0,2,6,8,14,15,16,17] d25 b0
  have b1 : a 25 ≠ 15 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 15 d24 c68 (by decide +kernel)
  have t1 : a 25 ∈ [0,2,6,8,16,17] := remove (a 25) 15 [0,2,6,8,15,16,17] t0 b1
  have b2 : a 25 ≠ 16 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 16 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,6,8,17] := remove (a 25) 16 [0,2,6,8,16,17] t1 b2
  have b3 : a 25 ≠ 17 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 17 d24 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,6,8] := remove (a 25) 17 [0,2,6,8,17] t2 b3
  have b4 : a 24 ≠ 2 := exclude [0,1,2,3,12,13] (edge r69) (a 24) (a 26) 2 d26 c69 (by decide +kernel)
  have t4 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b4
  have b5 : a 26 ≠ 2 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 2 t4 c69 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,3,12,13] := remove (a 26) 2 [0,1,2,3,12,13] d26 b5
  have b6 : a 26 ≠ 3 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 3 t4 c69 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,12,13] := remove (a 26) 3 [0,1,3,12,13] t5 b6
  have b7 : a 26 ≠ 12 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 12 t4 c69 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,13] := remove (a 26) 12 [0,1,12,13] t6 b7
  have b8 : a 26 ≠ 13 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 13 t4 c69 (by decide +kernel)
  have t8 : a 26 ∈ [0,1] := remove (a 26) 13 [0,1,13] t7 b8
  have b9 : a 28 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 2 t4 c70 (by decide +kernel)
  have t9 : a 28 ∈ [0,6,8] := remove (a 28) 2 [0,2,6,8] d28 b9
  have b10 : a 28 ≠ 8 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 8 t4 c70 (by decide +kernel)
  have t10 : a 28 ∈ [0,6] := remove (a 28) 8 [0,6,8] t9 b10
  have b11 : a 25 ≠ 2 := exclude [0,1,6,7,12,13] (edge r72) (a 25) (a 29) 2 d29 c72 (by decide +kernel)
  have t11 : a 25 ∈ [0,6,8] := remove (a 25) 2 [0,2,6,8] t3 b11
  have b12 : a 25 ≠ 8 := exclude [0,1,6,7,12,13] (edge r72) (a 25) (a 29) 8 d29 c72 (by decide +kernel)
  have t12 : a 25 ∈ [0,6] := remove (a 25) 8 [0,6,8] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0,6] (fun u v => edge r72 v u) (a 29) (a 25) 1 t12 c72 (by decide +kernel)
  have t13 : a 29 ∈ [0,6,7,12,13] := remove (a 29) 1 [0,1,6,7,12,13] d29 b13
  have b14 : a 29 ≠ 7 := exclude [0,6] (fun u v => edge r72 v u) (a 29) (a 25) 7 t12 c72 (by decide +kernel)
  have t14 : a 29 ∈ [0,6,12,13] := remove (a 29) 7 [0,6,7,12,13] t13 b14
  have b15 : a 29 ≠ 12 := exclude [0,6] (fun u v => edge r72 v u) (a 29) (a 25) 12 t12 c72 (by decide +kernel)
  have t15 : a 29 ∈ [0,6,13] := remove (a 29) 12 [0,6,12,13] t14 b15
  exact And.intro t12 (And.intro t4 (And.intro t8 (And.intro t10 (t15))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_194
