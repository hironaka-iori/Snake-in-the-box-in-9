import PartitionData205_179
namespace PartitionCover205_179
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d18 : a 18 ∈ [0,1,14,15])
    (d20 : a 20 ∈ [0,7,9,11])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d19 : a 19 ∈ [0,1,2])
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 16 ∈ [0,1,14,15] ∧ a 20 ∈ [0] ∧ a 17 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 16 ≠ 5 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 5 d18 c49 (by decide +kernel)
  have t0 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] d16 b0
  have b1 : a 16 ≠ 6 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 6 d18 c49 (by decide +kernel)
  have t1 : a 16 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 16 ≠ 7 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 7 d18 c49 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 16 ≠ 8 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 8 d18 c49 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 16) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 16 ≠ 9 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 9 d18 c49 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 16) 9 [0,1,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 16 ≠ 10 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 10 d18 c49 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 16) 10 [0,1,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 16 ≠ 11 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 11 d18 c49 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,12,13,14,15,16,17] := remove (a 16) 11 [0,1,11,12,13,14,15,16,17] t5 b6
  have b7 : a 16 ≠ 12 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 12 d18 c49 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,13,14,15,16,17] := remove (a 16) 12 [0,1,12,13,14,15,16,17] t6 b7
  have b8 : a 16 ≠ 13 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 13 d18 c49 (by decide +kernel)
  have t8 : a 16 ∈ [0,1,14,15,16,17] := remove (a 16) 13 [0,1,13,14,15,16,17] t7 b8
  have b9 : a 16 ≠ 16 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 16 d18 c49 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,14,15,17] := remove (a 16) 16 [0,1,14,15,16,17] t8 b9
  have b10 : a 16 ≠ 17 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 17 d18 c49 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,14,15] := remove (a 16) 17 [0,1,14,15,17] t9 b10
  have b11 : a 20 ≠ 7 := exclude [0,1,14,15] (fun u v => edge r50 v u) (a 20) (a 16) 7 t10 c50 (by decide +kernel)
  have t11 : a 20 ∈ [0,9,11] := remove (a 20) 7 [0,7,9,11] d20 b11
  have b12 : a 20 ≠ 9 := exclude [0,1,14,15] (fun u v => edge r50 v u) (a 20) (a 16) 9 t10 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,11] := remove (a 20) 9 [0,9,11] t11 b12
  have b13 : a 20 ≠ 11 := exclude [0,1,14,15] (fun u v => edge r50 v u) (a 20) (a 16) 11 t10 c50 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 11 [0,11] t12 b13
  have b14 : a 17 ≠ 6 := exclude [0,1,2] (edge r52) (a 17) (a 19) 6 d19 c52 (by decide +kernel)
  have t14 : a 17 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 17) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d17 b14
  have b15 : a 17 ≠ 7 := exclude [0,1,2] (edge r52) (a 17) (a 19) 7 d19 c52 (by decide +kernel)
  have t15 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 17) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t10 (And.intro t13 (t15))

theorem chunk9 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17])
    (d19 : a 19 ∈ [0,1,2])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0,1,14,15])
    (d22 : a 22 ∈ [0,4,6,9])
    (d26 : a 26 ∈ [0,5])
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 17 ∈ [0,1,2,3,4,5,8,9,10,11] ∧ a 21 ∈ [0,1,2,3,4,5,8,9,10,11] ∧ a 19 ∈ [0] ∧ a 18 ∈ [0,1] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 17 ≠ 12 := exclude [0,1,2] (edge r52) (a 17) (a 19) 12 d19 c52 (by decide +kernel)
  have t0 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] := remove (a 17) 12 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] d17 b0
  have b1 : a 17 ≠ 13 := exclude [0,1,2] (edge r52) (a 17) (a 19) 13 d19 c52 (by decide +kernel)
  have t1 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17] := remove (a 17) 13 [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] t0 b1
  have b2 : a 17 ≠ 14 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r53) (a 17) (a 21) 14 d21 c53 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11,15,16,17] := remove (a 17) 14 [0,1,2,3,4,5,8,9,10,11,14,15,16,17] t1 b2
  have b3 : a 17 ≠ 15 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r53) (a 17) (a 21) 15 d21 c53 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11,16,17] := remove (a 17) 15 [0,1,2,3,4,5,8,9,10,11,15,16,17] t2 b3
  have b4 : a 17 ≠ 16 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r53) (a 17) (a 21) 16 d21 c53 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11,17] := remove (a 17) 16 [0,1,2,3,4,5,8,9,10,11,16,17] t3 b4
  have b5 : a 17 ≠ 17 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r53) (a 17) (a 21) 17 d21 c53 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11] := remove (a 17) 17 [0,1,2,3,4,5,8,9,10,11,17] t4 b5
  have b6 : a 21 ≠ 6 := exclude [0,1,2,3,4,5,8,9,10,11] (fun u v => edge r53 v u) (a 21) (a 17) 6 t5 c53 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,2,3,4,5,7,8,9,10,11] := remove (a 21) 6 [0,1,2,3,4,5,6,7,8,9,10,11] d21 b6
  have b7 : a 21 ≠ 7 := exclude [0,1,2,3,4,5,8,9,10,11] (fun u v => edge r53 v u) (a 21) (a 17) 7 t5 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,2,3,4,5,8,9,10,11] := remove (a 21) 7 [0,1,2,3,4,5,7,8,9,10,11] t6 b7
  have b8 : a 19 ≠ 1 := exclude [0,1,14,15] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,2] := remove (a 19) 1 [0,1,2] d19 b8
  have b9 : a 19 ≠ 2 := exclude [0,1,14,15] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t9 : a 19 ∈ [0] := remove (a 19) 2 [0,2] t8 b9
  have b10 : a 18 ≠ 14 := exclude [0,4,6,9] (edge r56) (a 18) (a 22) 14 d22 c56 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,15] := remove (a 18) 14 [0,1,14,15] d18 b10
  have b11 : a 18 ≠ 15 := exclude [0,4,6,9] (edge r56) (a 18) (a 22) 15 d22 c56 (by decide +kernel)
  have t11 : a 18 ∈ [0,1] := remove (a 18) 15 [0,1,15] t10 b11
  have b12 : a 22 ≠ 4 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 4 t11 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,6,9] := remove (a 22) 4 [0,4,6,9] d22 b12
  have b13 : a 22 ≠ 6 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 6 t11 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,9] := remove (a 22) 6 [0,6,9] t12 b13
  have b14 : a 22 ≠ 9 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 9 t11 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0] := remove (a 22) 9 [0,9] t13 b14
  have b15 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r57 v u) (a 26) (a 18) 5 t11 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 5 [0,5] d26 b15
  exact And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t14 (t15)))))

theorem chunk10 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,12,13,14,15,16,17])
    (d19 : a 19 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3,4,5,8,9,10,11])
    (d20 : a 20 ∈ [0])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 23 ∈ [0,1,4,5] ∧ a 21 ∈ [0,1] := by
  have b0 : a 23 ≠ 12 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 12 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,2,3,4,5,13,14,15,16,17] := remove (a 23) 12 [0,1,2,3,4,5,12,13,14,15,16,17] d23 b0
  have b1 : a 23 ≠ 13 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 13 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,2,3,4,5,14,15,16,17] := remove (a 23) 13 [0,1,2,3,4,5,13,14,15,16,17] t0 b1
  have b2 : a 23 ≠ 14 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 14 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,1,2,3,4,5,15,16,17] := remove (a 23) 14 [0,1,2,3,4,5,14,15,16,17] t1 b2
  have b3 : a 23 ≠ 15 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 15 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,2,3,4,5,16,17] := remove (a 23) 15 [0,1,2,3,4,5,15,16,17] t2 b3
  have b4 : a 23 ≠ 16 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 16 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,2,3,4,5,17] := remove (a 23) 16 [0,1,2,3,4,5,16,17] t3 b4
  have b5 : a 23 ≠ 17 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 17 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,2,3,4,5] := remove (a 23) 17 [0,1,2,3,4,5,17] t4 b5
  have b6 : a 21 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 2 d20 c60 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,3,4,5,8,9,10,11] := remove (a 21) 2 [0,1,2,3,4,5,8,9,10,11] d21 b6
  have b7 : a 21 ≠ 3 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 3 d20 c60 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,4,5,8,9,10,11] := remove (a 21) 3 [0,1,3,4,5,8,9,10,11] t6 b7
  have b8 : a 21 ≠ 4 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 4 d20 c60 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,5,8,9,10,11] := remove (a 21) 4 [0,1,4,5,8,9,10,11] t7 b8
  have b9 : a 21 ≠ 5 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 5 d20 c60 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,8,9,10,11] := remove (a 21) 5 [0,1,5,8,9,10,11] t8 b9
  have b10 : a 21 ≠ 8 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 8 d20 c60 (by decide +kernel)
  have t10 : a 21 ∈ [0,1,9,10,11] := remove (a 21) 8 [0,1,8,9,10,11] t9 b10
  have b11 : a 21 ≠ 9 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 9 d20 c60 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,10,11] := remove (a 21) 9 [0,1,9,10,11] t10 b11
  have b12 : a 21 ≠ 10 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 10 d20 c60 (by decide +kernel)
  have t12 : a 21 ∈ [0,1,11] := remove (a 21) 10 [0,1,10,11] t11 b12
  have b13 : a 21 ≠ 11 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 11 d20 c60 (by decide +kernel)
  have t13 : a 21 ∈ [0,1] := remove (a 21) 11 [0,1,11] t12 b13
  have b14 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 2 t13 c63 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] t5 b14
  have b15 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 3 t13 c63 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,4,5] := remove (a 23) 3 [0,1,3,4,5] t14 b15
  exact And.intro t15 (t13)

theorem chunk11 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,4,5])
    (d21 : a 21 ∈ [0,1])
    (d31 : a 31 ∈ [0,6])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d26 : a 26 ∈ [0])
    (d28 : a 28 ∈ [0,1,2])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d27 : a 27 ∈ [0,1])
    (c63 : edge r63 (a 21) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    : a 23 ∈ [0] ∧ a 31 ∈ [0] ∧ a 24 ∈ [0,1] ∧ a 28 ∈ [0,2] ∧ a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 23 ≠ 4 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 4 d21 c63 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,5] := remove (a 23) 4 [0,1,4,5] d23 b0
  have b1 : a 23 ≠ 5 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 5 d21 c63 (by decide +kernel)
  have t1 : a 23 ∈ [0,1] := remove (a 23) 5 [0,1,5] t0 b1
  have b2 : a 23 ≠ 1 := exclude [0,6] (edge r67) (a 23) (a 31) 1 d31 c67 (by decide +kernel)
  have t2 : a 23 ∈ [0] := remove (a 23) 1 [0,1] t1 b2
  have b3 : a 31 ≠ 6 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 6 t2 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 6 [0,6] d31 b3
  have b4 : a 24 ≠ 2 := exclude [0] (edge r69) (a 24) (a 26) 2 d26 c69 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b4
  have b5 : a 24 ≠ 3 := exclude [0] (edge r69) (a 24) (a 26) 3 d26 c69 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 24 ≠ 4 := exclude [0] (edge r69) (a 24) (a 26) 4 d26 c69 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 24) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 24 ≠ 5 := exclude [0] (edge r69) (a 24) (a 26) 5 d26 c69 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,6,7,8,9,10,11] := remove (a 24) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 24 ≠ 6 := exclude [0] (edge r69) (a 24) (a 26) 6 d26 c69 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,7,8,9,10,11] := remove (a 24) 6 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 24 ≠ 7 := exclude [0] (edge r69) (a 24) (a 26) 7 d26 c69 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,8,9,10,11] := remove (a 24) 7 [0,1,7,8,9,10,11] t8 b9
  have b10 : a 24 ≠ 8 := exclude [0] (edge r69) (a 24) (a 26) 8 d26 c69 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,9,10,11] := remove (a 24) 8 [0,1,8,9,10,11] t9 b10
  have b11 : a 24 ≠ 9 := exclude [0] (edge r69) (a 24) (a 26) 9 d26 c69 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,10,11] := remove (a 24) 9 [0,1,9,10,11] t10 b11
  have b12 : a 24 ≠ 10 := exclude [0] (edge r69) (a 24) (a 26) 10 d26 c69 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,11] := remove (a 24) 10 [0,1,10,11] t11 b12
  have b13 : a 24 ≠ 11 := exclude [0] (edge r69) (a 24) (a 26) 11 d26 c69 (by decide +kernel)
  have t13 : a 24 ∈ [0,1] := remove (a 24) 11 [0,1,11] t12 b13
  have b14 : a 28 ≠ 1 := exclude [0,1] (fun u v => edge r70 v u) (a 28) (a 24) 1 t13 c70 (by decide +kernel)
  have t14 : a 28 ∈ [0,2] := remove (a 28) 1 [0,1,2] d28 b14
  have b15 : a 25 ≠ 2 := exclude [0,1] (edge r71) (a 25) (a 27) 2 d27 c71 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b15
  exact And.intro t2 (And.intro t3 (And.intro t13 (And.intro t14 (t15))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_179
