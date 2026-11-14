import PartitionData205_183
namespace PartitionCover205_183
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11])
    (d16 : a 16 ∈ [0,6])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d17 : a 17 ∈ [0])
    (c49 : edge r49 (a 16) (a 24)=true)
    (c50 : edge r50 (a 17) (a 18)=true)
    : a 24 ∈ [0,6] ∧ a 18 ∈ [0,2,10,11] := by
  have b0 : a 24 ≠ 3 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 3 d16 c49 (by decide +kernel)
  have t0 : a 24 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11] d24 b0
  have b1 : a 24 ≠ 4 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 4 d16 c49 (by decide +kernel)
  have t1 : a 24 ∈ [0,5,6,7,8,9,10,11] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 24 ≠ 5 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 5 d16 c49 (by decide +kernel)
  have t2 : a 24 ∈ [0,6,7,8,9,10,11] := remove (a 24) 5 [0,5,6,7,8,9,10,11] t1 b2
  have b3 : a 24 ≠ 7 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 7 d16 c49 (by decide +kernel)
  have t3 : a 24 ∈ [0,6,8,9,10,11] := remove (a 24) 7 [0,6,7,8,9,10,11] t2 b3
  have b4 : a 24 ≠ 8 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 8 d16 c49 (by decide +kernel)
  have t4 : a 24 ∈ [0,6,9,10,11] := remove (a 24) 8 [0,6,8,9,10,11] t3 b4
  have b5 : a 24 ≠ 9 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 9 d16 c49 (by decide +kernel)
  have t5 : a 24 ∈ [0,6,10,11] := remove (a 24) 9 [0,6,9,10,11] t4 b5
  have b6 : a 24 ≠ 10 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 10 d16 c49 (by decide +kernel)
  have t6 : a 24 ∈ [0,6,11] := remove (a 24) 10 [0,6,10,11] t5 b6
  have b7 : a 24 ≠ 11 := exclude [0,6] (fun u v => edge r49 v u) (a 24) (a 16) 11 d16 c49 (by decide +kernel)
  have t7 : a 24 ∈ [0,6] := remove (a 24) 11 [0,6,11] t6 b7
  have b8 : a 18 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 1 d17 c50 (by decide +kernel)
  have t8 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b8
  have b9 : a 18 ≠ 3 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 3 d17 c50 (by decide +kernel)
  have t9 : a 18 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 18) 3 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 18 ≠ 4 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 4 d17 c50 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 18) 4 [0,2,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 18 ≠ 5 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 5 d17 c50 (by decide +kernel)
  have t11 : a 18 ∈ [0,2,6,7,8,9,10,11] := remove (a 18) 5 [0,2,5,6,7,8,9,10,11] t10 b11
  have b12 : a 18 ≠ 6 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 6 d17 c50 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,7,8,9,10,11] := remove (a 18) 6 [0,2,6,7,8,9,10,11] t11 b12
  have b13 : a 18 ≠ 7 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 7 d17 c50 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,8,9,10,11] := remove (a 18) 7 [0,2,7,8,9,10,11] t12 b13
  have b14 : a 18 ≠ 8 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 8 d17 c50 (by decide +kernel)
  have t14 : a 18 ∈ [0,2,9,10,11] := remove (a 18) 8 [0,2,8,9,10,11] t13 b14
  have b15 : a 18 ≠ 9 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 9 d17 c50 (by decide +kernel)
  have t15 : a 18 ∈ [0,2,10,11] := remove (a 18) 9 [0,2,9,10,11] t14 b15
  exact And.intro t7 (t15)

theorem chunk13 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2,10,11])
    (d17 : a 17 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c50 : edge r50 (a 17) (a 18)=true)
    (c51 : edge r51 (a 17) (a 21)=true)
    : a 18 ∈ [0,2] ∧ a 21 ∈ [0,1,16,17] := by
  have b0 : a 18 ≠ 10 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 10 d17 c50 (by decide +kernel)
  have t0 : a 18 ∈ [0,2,11] := remove (a 18) 10 [0,2,10,11] d18 b0
  have b1 : a 18 ≠ 11 := exclude [0] (fun u v => edge r50 v u) (a 18) (a 17) 11 d17 c50 (by decide +kernel)
  have t1 : a 18 ∈ [0,2] := remove (a 18) 11 [0,2,11] t0 b1
  have b2 : a 21 ≠ 2 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 2 d17 c51 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d21 b2
  have b3 : a 21 ≠ 3 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 3 d17 c51 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 21 ≠ 4 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 4 d17 c51 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 21 ≠ 5 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 5 d17 c51 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 21 ≠ 6 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 6 d17 c51 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 21 ≠ 7 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 7 d17 c51 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 21 ≠ 8 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 8 d17 c51 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 21) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 21 ≠ 9 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 9 d17 c51 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 21) 9 [0,1,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 21 ≠ 10 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 10 d17 c51 (by decide +kernel)
  have t10 : a 21 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 21) 10 [0,1,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 21 ≠ 11 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 11 d17 c51 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,12,13,14,15,16,17] := remove (a 21) 11 [0,1,11,12,13,14,15,16,17] t10 b11
  have b12 : a 21 ≠ 12 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 12 d17 c51 (by decide +kernel)
  have t12 : a 21 ∈ [0,1,13,14,15,16,17] := remove (a 21) 12 [0,1,12,13,14,15,16,17] t11 b12
  have b13 : a 21 ≠ 13 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 13 d17 c51 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,14,15,16,17] := remove (a 21) 13 [0,1,13,14,15,16,17] t12 b13
  have b14 : a 21 ≠ 14 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 14 d17 c51 (by decide +kernel)
  have t14 : a 21 ∈ [0,1,15,16,17] := remove (a 21) 14 [0,1,14,15,16,17] t13 b14
  have b15 : a 21 ≠ 15 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 15 d17 c51 (by decide +kernel)
  have t15 : a 21 ∈ [0,1,16,17] := remove (a 21) 15 [0,1,15,16,17] t14 b15
  exact And.intro t1 (t15)

theorem chunk14 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,16,17])
    (d17 : a 17 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (d26 : a 26 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,2])
    (d19 : a 19 ∈ [0,1,6,7])
    (d20 : a 20 ∈ [0])
    (d27 : a 27 ∈ [0,2,6,8,10,11])
    (d28 : a 28 ∈ [0,1,2,3])
    (c51 : edge r51 (a 17) (a 21)=true)
    (c52 : edge r52 (a 17) (a 25)=true)
    (c54 : edge r54 (a 18) (a 26)=true)
    (c55 : edge r55 (a 19) (a 20)=true)
    (c57 : edge r57 (a 19) (a 27)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    : a 21 ∈ [0,1] ∧ a 25 ∈ [0,3] ∧ a 26 ∈ [0,2] ∧ a 19 ∈ [0,6] ∧ a 27 ∈ [0,6] ∧ a 28 ∈ [0,3] := by
  have b0 : a 21 ≠ 16 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 16 d17 c51 (by decide +kernel)
  have t0 : a 21 ∈ [0,1,17] := remove (a 21) 16 [0,1,16,17] d21 b0
  have b1 : a 21 ≠ 17 := exclude [0] (fun u v => edge r51 v u) (a 21) (a 17) 17 d17 c51 (by decide +kernel)
  have t1 : a 21 ∈ [0,1] := remove (a 21) 17 [0,1,17] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 25) (a 17) 1 d17 c52 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,3,4,5] := remove (a 25) 1 [0,1,2,3,4,5] d25 b2
  have b3 : a 25 ≠ 2 := exclude [0] (fun u v => edge r52 v u) (a 25) (a 17) 2 d17 c52 (by decide +kernel)
  have t3 : a 25 ∈ [0,3,4,5] := remove (a 25) 2 [0,2,3,4,5] t2 b3
  have b4 : a 25 ≠ 4 := exclude [0] (fun u v => edge r52 v u) (a 25) (a 17) 4 d17 c52 (by decide +kernel)
  have t4 : a 25 ∈ [0,3,5] := remove (a 25) 4 [0,3,4,5] t3 b4
  have b5 : a 25 ≠ 5 := exclude [0] (fun u v => edge r52 v u) (a 25) (a 17) 5 d17 c52 (by decide +kernel)
  have t5 : a 25 ∈ [0,3] := remove (a 25) 5 [0,3,5] t4 b5
  have b6 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r54 v u) (a 26) (a 18) 1 d18 c54 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b6
  have b7 : a 26 ≠ 3 := exclude [0,2] (fun u v => edge r54 v u) (a 26) (a 18) 3 d18 c54 (by decide +kernel)
  have t7 : a 26 ∈ [0,2] := remove (a 26) 3 [0,2,3] t6 b7
  have b8 : a 19 ≠ 1 := exclude [0] (edge r55) (a 19) (a 20) 1 d20 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,6,7] := remove (a 19) 1 [0,1,6,7] d19 b8
  have b9 : a 19 ≠ 7 := exclude [0] (edge r55) (a 19) (a 20) 7 d20 c55 (by decide +kernel)
  have t9 : a 19 ∈ [0,6] := remove (a 19) 7 [0,6,7] t8 b9
  have b10 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r57 v u) (a 27) (a 19) 2 t9 c57 (by decide +kernel)
  have t10 : a 27 ∈ [0,6,8,10,11] := remove (a 27) 2 [0,2,6,8,10,11] d27 b10
  have b11 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r57 v u) (a 27) (a 19) 8 t9 c57 (by decide +kernel)
  have t11 : a 27 ∈ [0,6,10,11] := remove (a 27) 8 [0,6,8,10,11] t10 b11
  have b12 : a 27 ≠ 10 := exclude [0,6] (fun u v => edge r57 v u) (a 27) (a 19) 10 t9 c57 (by decide +kernel)
  have t12 : a 27 ∈ [0,6,11] := remove (a 27) 10 [0,6,10,11] t11 b12
  have b13 : a 27 ≠ 11 := exclude [0,6] (fun u v => edge r57 v u) (a 27) (a 19) 11 t9 c57 (by decide +kernel)
  have t13 : a 27 ∈ [0,6] := remove (a 27) 11 [0,6,11] t12 b13
  have b14 : a 28 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 28) (a 20) 1 d20 c59 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b14
  have b15 : a 28 ≠ 2 := exclude [0] (fun u v => edge r59 v u) (a 28) (a 20) 2 d20 c59 (by decide +kernel)
  have t15 : a 28 ∈ [0,3] := remove (a 28) 2 [0,2,3] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk15 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,3])
    (d20 : a 20 ∈ [0])
    (d29 : a 29 ∈ [0,1,6,7,12,13])
    (d21 : a 21 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,3,12,13,15])
    (c41 : edge r41 (a 13) (a 28)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    (c61 : edge r61 (a 21) (a 29)=true)
    (c62 : edge r62 (a 22) (a 30)=true)
    : a 28 ∈ [0] ∧ a 29 ∈ [0,1] ∧ a 30 ∈ [0,2] ∧ a 13 ∈ [0,12] := by
  have b0 : a 28 ≠ 3 := exclude [0] (fun u v => edge r59 v u) (a 28) (a 20) 3 d20 c59 (by decide +kernel)
  have t0 : a 28 ∈ [0] := remove (a 28) 3 [0,3] d28 b0
  have b1 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r61 v u) (a 29) (a 21) 6 d21 c61 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,7,12,13] := remove (a 29) 6 [0,1,6,7,12,13] d29 b1
  have b2 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r61 v u) (a 29) (a 21) 7 d21 c61 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,12,13] := remove (a 29) 7 [0,1,7,12,13] t1 b2
  have b3 : a 29 ≠ 12 := exclude [0,1] (fun u v => edge r61 v u) (a 29) (a 21) 12 d21 c61 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,13] := remove (a 29) 12 [0,1,12,13] t2 b3
  have b4 : a 29 ≠ 13 := exclude [0,1] (fun u v => edge r61 v u) (a 29) (a 21) 13 d21 c61 (by decide +kernel)
  have t4 : a 29 ∈ [0,1] := remove (a 29) 13 [0,1,13] t3 b4
  have b5 : a 30 ≠ 1 := exclude [0,2] (fun u v => edge r62 v u) (a 30) (a 22) 1 d22 c62 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,3,4,5] := remove (a 30) 1 [0,1,2,3,4,5] d30 b5
  have b6 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r62 v u) (a 30) (a 22) 3 d22 c62 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,4,5] := remove (a 30) 3 [0,2,3,4,5] t5 b6
  have b7 : a 30 ≠ 4 := exclude [0,2] (fun u v => edge r62 v u) (a 30) (a 22) 4 d22 c62 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,5] := remove (a 30) 4 [0,2,4,5] t6 b7
  have b8 : a 30 ≠ 5 := exclude [0,2] (fun u v => edge r62 v u) (a 30) (a 22) 5 d22 c62 (by decide +kernel)
  have t8 : a 30 ∈ [0,2] := remove (a 30) 5 [0,2,5] t7 b8
  have b9 : a 13 ≠ 1 := exclude [0] (edge r41) (a 13) (a 28) 1 t0 c41 (by decide +kernel)
  have t9 : a 13 ∈ [0,3,12,13,15] := remove (a 13) 1 [0,1,3,12,13,15] d13 b9
  have b10 : a 13 ≠ 3 := exclude [0] (edge r41) (a 13) (a 28) 3 t0 c41 (by decide +kernel)
  have t10 : a 13 ∈ [0,12,13,15] := remove (a 13) 3 [0,3,12,13,15] t9 b10
  have b11 : a 13 ≠ 13 := exclude [0] (edge r41) (a 13) (a 28) 13 t0 c41 (by decide +kernel)
  have t11 : a 13 ∈ [0,12,15] := remove (a 13) 13 [0,12,13,15] t10 b11
  have b12 : a 13 ≠ 15 := exclude [0] (edge r41) (a 13) (a 28) 15 t0 c41 (by decide +kernel)
  have t12 : a 13 ∈ [0,12] := remove (a 13) 15 [0,12,15] t11 b12
  exact And.intro t0 (And.intro t4 (And.intro t8 (t12)))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_183
