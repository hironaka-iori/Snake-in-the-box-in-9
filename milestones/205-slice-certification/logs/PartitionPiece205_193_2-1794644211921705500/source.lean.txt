import PartitionData205_193
namespace PartitionCover205_193
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,6,9])
    (d14 : a 14 ∈ [0,6])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d15 : a 15 ∈ [0])
    (d17 : a 17 ∈ [0,1,3,4,6,7])
    (d16 : a 16 ∈ [0,3])
    (d18 : a 18 ∈ [0,2,6,8,12,14])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    : a 30 ∈ [0,6] ∧ a 31 ∈ [0,1] ∧ a 17 ∈ [0,3] ∧ a 18 ∈ [0,6,14] := by
  have b0 : a 30 ≠ 9 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,6] := remove (a 30) 9 [0,6,9] d30 b0
  have b1 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9] d31 b1
  have b2 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,4,5,6,7,8,9] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9] t1 b2
  have b3 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,5,6,7,8,9] := remove (a 31) 4 [0,1,4,5,6,7,8,9] t2 b3
  have b4 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,6,7,8,9] := remove (a 31) 5 [0,1,5,6,7,8,9] t3 b4
  have b5 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,7,8,9] := remove (a 31) 6 [0,1,6,7,8,9] t4 b5
  have b6 : a 31 ≠ 7 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,8,9] := remove (a 31) 7 [0,1,7,8,9] t5 b6
  have b7 : a 31 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,9] := remove (a 31) 8 [0,1,8,9] t6 b7
  have b8 : a 31 ≠ 9 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1] := remove (a 31) 9 [0,1,9] t7 b8
  have b9 : a 17 ≠ 1 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 1 d16 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0,3,4,6,7] := remove (a 17) 1 [0,1,3,4,6,7] d17 b9
  have b10 : a 17 ≠ 4 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 4 d16 c48 (by decide +kernel)
  have t10 : a 17 ∈ [0,3,6,7] := remove (a 17) 4 [0,3,4,6,7] t9 b10
  have b11 : a 17 ≠ 6 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 6 d16 c48 (by decide +kernel)
  have t11 : a 17 ∈ [0,3,7] := remove (a 17) 6 [0,3,6,7] t10 b11
  have b12 : a 17 ≠ 7 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 7 d16 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,3] := remove (a 17) 7 [0,3,7] t11 b12
  have b13 : a 18 ≠ 2 := exclude [0,3] (fun u v => edge r49 v u) (a 18) (a 16) 2 d16 c49 (by decide +kernel)
  have t13 : a 18 ∈ [0,6,8,12,14] := remove (a 18) 2 [0,2,6,8,12,14] d18 b13
  have b14 : a 18 ≠ 8 := exclude [0,3] (fun u v => edge r49 v u) (a 18) (a 16) 8 d16 c49 (by decide +kernel)
  have t14 : a 18 ∈ [0,6,12,14] := remove (a 18) 8 [0,6,8,12,14] t13 b14
  have b15 : a 18 ≠ 12 := exclude [0,3] (fun u v => edge r49 v u) (a 18) (a 16) 12 d16 c49 (by decide +kernel)
  have t15 : a 18 ∈ [0,6,14] := remove (a 18) 12 [0,6,12,14] t14 b15
  exact And.intro t0 (And.intro t8 (And.intro t12 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,6,14])
    (d16 : a 16 ∈ [0,3])
    (d20 : a 20 ∈ [0,2,4,5,6,8,10,11,12,14,16,17])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (d17 : a 17 ∈ [0,3])
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 18 ∈ [0,6] ∧ a 20 ∈ [0,6] ∧ a 21 ∈ [0,3,7,8] := by
  have b0 : a 18 ≠ 14 := exclude [0,3] (fun u v => edge r49 v u) (a 18) (a 16) 14 d16 c49 (by decide +kernel)
  have t0 : a 18 ∈ [0,6] := remove (a 18) 14 [0,6,14] d18 b0
  have b1 : a 20 ≠ 2 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 2 d16 c50 (by decide +kernel)
  have t1 : a 20 ∈ [0,4,5,6,8,10,11,12,14,16,17] := remove (a 20) 2 [0,2,4,5,6,8,10,11,12,14,16,17] d20 b1
  have b2 : a 20 ≠ 4 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 4 d16 c50 (by decide +kernel)
  have t2 : a 20 ∈ [0,5,6,8,10,11,12,14,16,17] := remove (a 20) 4 [0,4,5,6,8,10,11,12,14,16,17] t1 b2
  have b3 : a 20 ≠ 5 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 5 d16 c50 (by decide +kernel)
  have t3 : a 20 ∈ [0,6,8,10,11,12,14,16,17] := remove (a 20) 5 [0,5,6,8,10,11,12,14,16,17] t2 b3
  have b4 : a 20 ≠ 8 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 8 d16 c50 (by decide +kernel)
  have t4 : a 20 ∈ [0,6,10,11,12,14,16,17] := remove (a 20) 8 [0,6,8,10,11,12,14,16,17] t3 b4
  have b5 : a 20 ≠ 10 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 10 d16 c50 (by decide +kernel)
  have t5 : a 20 ∈ [0,6,11,12,14,16,17] := remove (a 20) 10 [0,6,10,11,12,14,16,17] t4 b5
  have b6 : a 20 ≠ 11 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 11 d16 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0,6,12,14,16,17] := remove (a 20) 11 [0,6,11,12,14,16,17] t5 b6
  have b7 : a 20 ≠ 12 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 12 d16 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0,6,14,16,17] := remove (a 20) 12 [0,6,12,14,16,17] t6 b7
  have b8 : a 20 ≠ 14 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 14 d16 c50 (by decide +kernel)
  have t8 : a 20 ∈ [0,6,16,17] := remove (a 20) 14 [0,6,14,16,17] t7 b8
  have b9 : a 20 ≠ 16 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 16 d16 c50 (by decide +kernel)
  have t9 : a 20 ∈ [0,6,17] := remove (a 20) 16 [0,6,16,17] t8 b9
  have b10 : a 20 ≠ 17 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 17 d16 c50 (by decide +kernel)
  have t10 : a 20 ∈ [0,6] := remove (a 20) 17 [0,6,17] t9 b10
  have b11 : a 21 ≠ 1 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,3,4,5,6,7,8] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8] d21 b11
  have b12 : a 21 ≠ 2 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t12 : a 21 ∈ [0,3,4,5,6,7,8] := remove (a 21) 2 [0,2,3,4,5,6,7,8] t11 b12
  have b13 : a 21 ≠ 4 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t13 : a 21 ∈ [0,3,5,6,7,8] := remove (a 21) 4 [0,3,4,5,6,7,8] t12 b13
  have b14 : a 21 ≠ 5 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t14 : a 21 ∈ [0,3,6,7,8] := remove (a 21) 5 [0,3,5,6,7,8] t13 b14
  have b15 : a 21 ≠ 6 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 6 d17 c53 (by decide +kernel)
  have t15 : a 21 ∈ [0,3,7,8] := remove (a 21) 6 [0,3,6,7,8] t14 b15
  exact And.intro t0 (And.intro t10 (t15))

theorem chunk10 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,3,7,8])
    (d17 : a 17 ∈ [0,3])
    (d19 : a 19 ∈ [0,1])
    (d18 : a 18 ∈ [0,6])
    (d22 : a 22 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 21 ∈ [0,3] ∧ a 19 ∈ [0] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0,5,6,9] ∧ a 23 ∈ [0,2] := by
  have b0 : a 21 ≠ 7 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 7 d17 c53 (by decide +kernel)
  have t0 : a 21 ∈ [0,3,8] := remove (a 21) 7 [0,3,7,8] d21 b0
  have b1 : a 21 ≠ 8 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 8 d17 c53 (by decide +kernel)
  have t1 : a 21 ∈ [0,3] := remove (a 21) 8 [0,3,8] t0 b1
  have b2 : a 19 ≠ 1 := exclude [0,6] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t2 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b2
  have b3 : a 22 ≠ 1 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t3 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b3
  have b4 : a 22 ≠ 2 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 2 d18 c56 (by decide +kernel)
  have t4 : a 22 ∈ [0,3] := remove (a 22) 2 [0,2,3] t3 b4
  have b5 : a 22 ≠ 3 := exclude [0,6] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t5 : a 22 ∈ [0] := remove (a 22) 3 [0,3] t4 b5
  have b6 : a 26 ≠ 1 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 1 d18 c57 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9] d26 b6
  have b7 : a 26 ≠ 2 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 2 d18 c57 (by decide +kernel)
  have t7 : a 26 ∈ [0,3,4,5,6,7,8,9] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9] t6 b7
  have b8 : a 26 ≠ 3 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 3 d18 c57 (by decide +kernel)
  have t8 : a 26 ∈ [0,4,5,6,7,8,9] := remove (a 26) 3 [0,3,4,5,6,7,8,9] t7 b8
  have b9 : a 26 ≠ 4 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 4 d18 c57 (by decide +kernel)
  have t9 : a 26 ∈ [0,5,6,7,8,9] := remove (a 26) 4 [0,4,5,6,7,8,9] t8 b9
  have b10 : a 26 ≠ 7 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 7 d18 c57 (by decide +kernel)
  have t10 : a 26 ∈ [0,5,6,8,9] := remove (a 26) 7 [0,5,6,7,8,9] t9 b10
  have b11 : a 26 ≠ 8 := exclude [0,6] (fun u v => edge r57 v u) (a 26) (a 18) 8 d18 c57 (by decide +kernel)
  have t11 : a 26 ∈ [0,5,6,9] := remove (a 26) 8 [0,5,6,8,9] t10 b11
  have b12 : a 23 ≠ 3 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 3 t2 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,4,5] := remove (a 23) 3 [0,1,2,3,4,5] d23 b12
  have b13 : a 23 ≠ 4 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 4 t2 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,2,5] := remove (a 23) 4 [0,1,2,4,5] t12 b13
  have b14 : a 23 ≠ 5 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 5 t2 c58 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,2] := remove (a 23) 5 [0,1,2,5] t13 b14
  have b15 : a 23 ≠ 1 := exclude [0,3] (fun u v => edge r63 v u) (a 23) (a 21) 1 t1 c63 (by decide +kernel)
  have t15 : a 23 ∈ [0,2] := remove (a 23) 1 [0,1,2] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t5 (And.intro t11 (t15))))

theorem chunk11 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,2])
    (d21 : a 21 ∈ [0,3])
    (d29 : a 29 ∈ [0,1,6,7])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d24 : a 24 ∈ [0,2])
    (d26 : a 26 ∈ [0,5,6,9])
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 23 ∈ [0] ∧ a 29 ∈ [0,6] ∧ a 25 ∈ [0,6] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0,6] := by
  have b0 : a 23 ≠ 2 := exclude [0,3] (fun u v => edge r63 v u) (a 23) (a 21) 2 d21 c63 (by decide +kernel)
  have t0 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b0
  have b1 : a 29 ≠ 1 := exclude [0,3] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0,6,7] := remove (a 29) 1 [0,1,6,7] d29 b1
  have b2 : a 29 ≠ 7 := exclude [0,3] (fun u v => edge r64 v u) (a 29) (a 21) 7 d21 c64 (by decide +kernel)
  have t2 : a 29 ∈ [0,6] := remove (a 29) 7 [0,6,7] t1 b2
  have b3 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b3
  have b4 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 3 d24 c68 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 25 ≠ 4 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 25) 4 [0,2,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 5 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,6,7,8,9,10,11] := remove (a 25) 5 [0,2,5,6,7,8,9,10,11] t5 b6
  have b7 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 7 d24 c68 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,6,8,9,10,11] := remove (a 25) 7 [0,2,6,7,8,9,10,11] t6 b7
  have b8 : a 25 ≠ 9 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 9 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,6,8,10,11] := remove (a 25) 9 [0,2,6,8,9,10,11] t7 b8
  have b9 : a 25 ≠ 10 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 10 d24 c68 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,6,8,11] := remove (a 25) 10 [0,2,6,8,10,11] t8 b9
  have b10 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 11 d24 c68 (by decide +kernel)
  have t10 : a 25 ∈ [0,2,6,8] := remove (a 25) 11 [0,2,6,8,11] t9 b10
  have b11 : a 24 ≠ 2 := exclude [0,5,6,9] (edge r69) (a 24) (a 26) 2 d26 c69 (by decide +kernel)
  have t11 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b11
  have b12 : a 26 ≠ 5 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 5 t11 c69 (by decide +kernel)
  have t12 : a 26 ∈ [0,6,9] := remove (a 26) 5 [0,5,6,9] d26 b12
  have b13 : a 26 ≠ 9 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 9 t11 c69 (by decide +kernel)
  have t13 : a 26 ∈ [0,6] := remove (a 26) 9 [0,6,9] t12 b13
  have b14 : a 25 ≠ 2 := exclude [0,6] (edge r72) (a 25) (a 29) 2 t2 c72 (by decide +kernel)
  have t14 : a 25 ∈ [0,6,8] := remove (a 25) 2 [0,2,6,8] t10 b14
  have b15 : a 25 ≠ 8 := exclude [0,6] (edge r72) (a 25) (a 29) 8 t2 c72 (by decide +kernel)
  have t15 : a 25 ∈ [0,6] := remove (a 25) 8 [0,6,8] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t15 (And.intro t11 (t13))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_193
