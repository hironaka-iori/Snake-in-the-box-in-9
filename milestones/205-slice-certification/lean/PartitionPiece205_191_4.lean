import PartitionData205_191
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,9])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,21])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 30 ∈ [0,1,4,5] ∧ a 31 ∈ [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 30 ≠ 15 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := remove (a 30) 15 [0,1,4,5,15,16,17,18,19,20,21,22,23] d30 b0
  have b1 : a 30 ≠ 16 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,4,5,17,18,19,20,21,22,23] := remove (a 30) 16 [0,1,4,5,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 30 ≠ 17 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,4,5,18,19,20,21,22,23] := remove (a 30) 17 [0,1,4,5,17,18,19,20,21,22,23] t1 b2
  have b3 : a 30 ≠ 18 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,4,5,19,20,21,22,23] := remove (a 30) 18 [0,1,4,5,18,19,20,21,22,23] t2 b3
  have b4 : a 30 ≠ 19 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 19 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,4,5,20,21,22,23] := remove (a 30) 19 [0,1,4,5,19,20,21,22,23] t3 b4
  have b5 : a 30 ≠ 20 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 20 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,4,5,21,22,23] := remove (a 30) 20 [0,1,4,5,20,21,22,23] t4 b5
  have b6 : a 30 ≠ 21 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 21 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,4,5,22,23] := remove (a 30) 21 [0,1,4,5,21,22,23] t5 b6
  have b7 : a 30 ≠ 22 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 22 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,4,5,23] := remove (a 30) 22 [0,1,4,5,22,23] t6 b7
  have b8 : a 30 ≠ 23 := exclude [0,9] (fun u v => edge r46 v u) (a 30) (a 14) 23 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,4,5] := remove (a 30) 23 [0,1,4,5,23] t7 b8
  have b9 : a 31 ≠ 1 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b9
  have b10 : a 31 ≠ 2 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 31 ≠ 4 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 31 ≠ 5 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 31 ≠ 6 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 6 [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 31 ≠ 7 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 7 [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 31 ≠ 8 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 8 [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t8 (t15)

theorem chunk17 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d15 : a 15 ∈ [0,21])
    (d17 : a 17 ∈ [0,1,2,3,5,6,7,8,14,15,16,17])
    (d16 : a 16 ∈ [0,2,5,6,7,10])
    (d20 : a 20 ∈ [0,1,2,3])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    : a 31 ∈ [0,3,18,19] ∧ a 17 ∈ [0,1,3,5,6,7,8,14,16,17] ∧ a 16 ∈ [0,5,6,7,10] := by
  have b0 : a 31 ≠ 9 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 9 [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b0
  have b1 : a 31 ≠ 10 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,3,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 10 [0,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 31 ≠ 11 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,3,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 11 [0,3,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 31 ≠ 12 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 12 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,3,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 12 [0,3,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 31 ≠ 13 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 13 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,3,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 13 [0,3,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 31 ≠ 14 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 14 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,3,15,16,17,18,19,20,21,22,23] := remove (a 31) 14 [0,3,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 31 ≠ 15 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 15 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,3,16,17,18,19,20,21,22,23] := remove (a 31) 15 [0,3,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 31 ≠ 16 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,3,17,18,19,20,21,22,23] := remove (a 31) 16 [0,3,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 31 ≠ 17 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,3,18,19,20,21,22,23] := remove (a 31) 17 [0,3,17,18,19,20,21,22,23] t7 b8
  have b9 : a 31 ≠ 20 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 20 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,3,18,19,21,22,23] := remove (a 31) 20 [0,3,18,19,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 21 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 21 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,3,18,19,22,23] := remove (a 31) 21 [0,3,18,19,21,22,23] t9 b10
  have b11 : a 31 ≠ 22 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 22 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,3,18,19,23] := remove (a 31) 22 [0,3,18,19,22,23] t10 b11
  have b12 : a 31 ≠ 23 := exclude [0,21] (fun u v => edge r47 v u) (a 31) (a 15) 23 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,3,18,19] := remove (a 31) 23 [0,3,18,19,23] t11 b12
  have b13 : a 17 ≠ 2 := exclude [0,2,5,6,7,10] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0,1,3,5,6,7,8,14,15,16,17] := remove (a 17) 2 [0,1,2,3,5,6,7,8,14,15,16,17] d17 b13
  have b14 : a 17 ≠ 15 := exclude [0,2,5,6,7,10] (fun u v => edge r48 v u) (a 17) (a 16) 15 d16 c48 (by decide +kernel)
  have t14 : a 17 ∈ [0,1,3,5,6,7,8,14,16,17] := remove (a 17) 15 [0,1,3,5,6,7,8,14,15,16,17] t13 b14
  have b15 : a 16 ≠ 2 := exclude [0,1,2,3] (edge r50) (a 16) (a 20) 2 d20 c50 (by decide +kernel)
  have t15 : a 16 ∈ [0,5,6,7,10] := remove (a 16) 2 [0,2,5,6,7,10] d16 b15
  exact And.intro t12 (And.intro t14 (t15))

theorem chunk18 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,5,6,7,10])
    (d20 : a 20 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,4,5,16])
    (d17 : a 17 ∈ [0,1,3,5,6,7,8,14,16,17])
    (d21 : a 21 ∈ [0,4])
    (d18 : a 18 ∈ [0,1,2,3,6,10,11,12,13,14,15,18,19,20,21,22])
    (d22 : a 22 ∈ [0,3])
    (d26 : a 26 ∈ [0,1,2,12])
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 16 ∈ [0,5,6,7] ∧ a 20 ∈ [0,3] ∧ a 24 ∈ [0,16] ∧ a 17 ∈ [0,1,3,14] ∧ a 18 ∈ [0,10,11,12,13,14,15,18,19,20,21] := by
  have b0 : a 16 ≠ 10 := exclude [0,1,2,3] (edge r50) (a 16) (a 20) 10 d20 c50 (by decide +kernel)
  have t0 : a 16 ∈ [0,5,6,7] := remove (a 16) 10 [0,5,6,7,10] d16 b0
  have b1 : a 20 ≠ 1 := exclude [0,5,6,7] (fun u v => edge r50 v u) (a 20) (a 16) 1 t0 c50 (by decide +kernel)
  have t1 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b1
  have b2 : a 20 ≠ 2 := exclude [0,5,6,7] (fun u v => edge r50 v u) (a 20) (a 16) 2 t0 c50 (by decide +kernel)
  have t2 : a 20 ∈ [0,3] := remove (a 20) 2 [0,2,3] t1 b2
  have b3 : a 24 ≠ 4 := exclude [0,5,6,7] (fun u v => edge r51 v u) (a 24) (a 16) 4 t0 c51 (by decide +kernel)
  have t3 : a 24 ∈ [0,5,16] := remove (a 24) 4 [0,4,5,16] d24 b3
  have b4 : a 24 ≠ 5 := exclude [0,5,6,7] (fun u v => edge r51 v u) (a 24) (a 16) 5 t0 c51 (by decide +kernel)
  have t4 : a 24 ∈ [0,16] := remove (a 24) 5 [0,5,16] t3 b4
  have b5 : a 17 ≠ 5 := exclude [0,4] (edge r53) (a 17) (a 21) 5 d21 c53 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,3,6,7,8,14,16,17] := remove (a 17) 5 [0,1,3,5,6,7,8,14,16,17] d17 b5
  have b6 : a 17 ≠ 6 := exclude [0,4] (edge r53) (a 17) (a 21) 6 d21 c53 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,3,7,8,14,16,17] := remove (a 17) 6 [0,1,3,6,7,8,14,16,17] t5 b6
  have b7 : a 17 ≠ 7 := exclude [0,4] (edge r53) (a 17) (a 21) 7 d21 c53 (by decide +kernel)
  have t7 : a 17 ∈ [0,1,3,8,14,16,17] := remove (a 17) 7 [0,1,3,7,8,14,16,17] t6 b7
  have b8 : a 17 ≠ 8 := exclude [0,4] (edge r53) (a 17) (a 21) 8 d21 c53 (by decide +kernel)
  have t8 : a 17 ∈ [0,1,3,14,16,17] := remove (a 17) 8 [0,1,3,8,14,16,17] t7 b8
  have b9 : a 17 ≠ 16 := exclude [0,4] (edge r53) (a 17) (a 21) 16 d21 c53 (by decide +kernel)
  have t9 : a 17 ∈ [0,1,3,14,17] := remove (a 17) 16 [0,1,3,14,16,17] t8 b9
  have b10 : a 17 ≠ 17 := exclude [0,4] (edge r53) (a 17) (a 21) 17 d21 c53 (by decide +kernel)
  have t10 : a 17 ∈ [0,1,3,14] := remove (a 17) 17 [0,1,3,14,17] t9 b10
  have b11 : a 18 ≠ 2 := exclude [0,3] (edge r56) (a 18) (a 22) 2 d22 c56 (by decide +kernel)
  have t11 : a 18 ∈ [0,1,3,6,10,11,12,13,14,15,18,19,20,21,22] := remove (a 18) 2 [0,1,2,3,6,10,11,12,13,14,15,18,19,20,21,22] d18 b11
  have b12 : a 18 ≠ 3 := exclude [0,3] (edge r56) (a 18) (a 22) 3 d22 c56 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,6,10,11,12,13,14,15,18,19,20,21,22] := remove (a 18) 3 [0,1,3,6,10,11,12,13,14,15,18,19,20,21,22] t11 b12
  have b13 : a 18 ≠ 6 := exclude [0,3] (edge r56) (a 18) (a 22) 6 d22 c56 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,10,11,12,13,14,15,18,19,20,21,22] := remove (a 18) 6 [0,1,6,10,11,12,13,14,15,18,19,20,21,22] t12 b13
  have b14 : a 18 ≠ 22 := exclude [0,3] (edge r56) (a 18) (a 22) 22 d22 c56 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,10,11,12,13,14,15,18,19,20,21] := remove (a 18) 22 [0,1,10,11,12,13,14,15,18,19,20,21,22] t13 b14
  have b15 : a 18 ≠ 1 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 1 d26 c57 (by decide +kernel)
  have t15 : a 18 ∈ [0,10,11,12,13,14,15,18,19,20,21] := remove (a 18) 1 [0,1,10,11,12,13,14,15,18,19,20,21] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t10 (t15))))

theorem chunk19 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,10,11,12,13,14,15,18,19,20,21])
    (d26 : a 26 ∈ [0,1,2,12])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,12,13,16,17,18,19])
    (d21 : a 21 ∈ [0,4])
    (c57 : edge r57 (a 18) (a 26)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 18 ∈ [0,13,15,19] ∧ a 23 ∈ [0,12,17,18,19] := by
  have b0 : a 18 ≠ 10 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 10 d26 c57 (by decide +kernel)
  have t0 : a 18 ∈ [0,11,12,13,14,15,18,19,20,21] := remove (a 18) 10 [0,10,11,12,13,14,15,18,19,20,21] d18 b0
  have b1 : a 18 ≠ 11 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 11 d26 c57 (by decide +kernel)
  have t1 : a 18 ∈ [0,12,13,14,15,18,19,20,21] := remove (a 18) 11 [0,11,12,13,14,15,18,19,20,21] t0 b1
  have b2 : a 18 ≠ 12 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 12 d26 c57 (by decide +kernel)
  have t2 : a 18 ∈ [0,13,14,15,18,19,20,21] := remove (a 18) 12 [0,12,13,14,15,18,19,20,21] t1 b2
  have b3 : a 18 ≠ 14 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 14 d26 c57 (by decide +kernel)
  have t3 : a 18 ∈ [0,13,15,18,19,20,21] := remove (a 18) 14 [0,13,14,15,18,19,20,21] t2 b3
  have b4 : a 18 ≠ 18 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 18 d26 c57 (by decide +kernel)
  have t4 : a 18 ∈ [0,13,15,19,20,21] := remove (a 18) 18 [0,13,15,18,19,20,21] t3 b4
  have b5 : a 18 ≠ 20 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 20 d26 c57 (by decide +kernel)
  have t5 : a 18 ∈ [0,13,15,19,21] := remove (a 18) 20 [0,13,15,19,20,21] t4 b5
  have b6 : a 18 ≠ 21 := exclude [0,1,2,12] (edge r57) (a 18) (a 26) 21 d26 c57 (by decide +kernel)
  have t6 : a 18 ∈ [0,13,15,19] := remove (a 18) 21 [0,13,15,19,21] t5 b6
  have b7 : a 23 ≠ 1 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 1 d21 c63 (by decide +kernel)
  have t7 : a 23 ∈ [0,2,3,4,5,6,7,12,13,16,17,18,19] := remove (a 23) 1 [0,1,2,3,4,5,6,7,12,13,16,17,18,19] d23 b7
  have b8 : a 23 ≠ 2 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 2 d21 c63 (by decide +kernel)
  have t8 : a 23 ∈ [0,3,4,5,6,7,12,13,16,17,18,19] := remove (a 23) 2 [0,2,3,4,5,6,7,12,13,16,17,18,19] t7 b8
  have b9 : a 23 ≠ 3 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 3 d21 c63 (by decide +kernel)
  have t9 : a 23 ∈ [0,4,5,6,7,12,13,16,17,18,19] := remove (a 23) 3 [0,3,4,5,6,7,12,13,16,17,18,19] t8 b9
  have b10 : a 23 ≠ 4 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 4 d21 c63 (by decide +kernel)
  have t10 : a 23 ∈ [0,5,6,7,12,13,16,17,18,19] := remove (a 23) 4 [0,4,5,6,7,12,13,16,17,18,19] t9 b10
  have b11 : a 23 ≠ 5 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 5 d21 c63 (by decide +kernel)
  have t11 : a 23 ∈ [0,6,7,12,13,16,17,18,19] := remove (a 23) 5 [0,5,6,7,12,13,16,17,18,19] t10 b11
  have b12 : a 23 ≠ 6 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 6 d21 c63 (by decide +kernel)
  have t12 : a 23 ∈ [0,7,12,13,16,17,18,19] := remove (a 23) 6 [0,6,7,12,13,16,17,18,19] t11 b12
  have b13 : a 23 ≠ 7 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 7 d21 c63 (by decide +kernel)
  have t13 : a 23 ∈ [0,12,13,16,17,18,19] := remove (a 23) 7 [0,7,12,13,16,17,18,19] t12 b13
  have b14 : a 23 ≠ 13 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 13 d21 c63 (by decide +kernel)
  have t14 : a 23 ∈ [0,12,16,17,18,19] := remove (a 23) 13 [0,12,13,16,17,18,19] t13 b14
  have b15 : a 23 ≠ 16 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 16 d21 c63 (by decide +kernel)
  have t15 : a 23 ∈ [0,12,17,18,19] := remove (a 23) 16 [0,12,16,17,18,19] t14 b15
  exact And.intro t6 (t15)

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_191
