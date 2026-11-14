import PartitionData205_208
namespace PartitionCover205_208
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,6,7,10,11])
    (d16 : a 16 ∈ [0,3])
    (d21 : a 21 ∈ [0,2,6,8])
    (d17 : a 17 ∈ [0,3])
    (d18 : a 18 ∈ [0,2])
    (d19 : a 19 ∈ [0,3])
    (d22 : a 22 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,6,7])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 20 ∈ [0,1,6,7] ∧ a 21 ∈ [0,6] ∧ a 18 ∈ [0] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0,1,6] ∧ a 27 ∈ [0,4,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 20 ≠ 10 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 10 d16 c50 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,6,7,11] := remove (a 20) 10 [0,1,6,7,10,11] d20 b0
  have b1 : a 20 ≠ 11 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 11 d16 c50 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,6,7] := remove (a 20) 11 [0,1,6,7,11] t0 b1
  have b2 : a 21 ≠ 2 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t2 : a 21 ∈ [0,6,8] := remove (a 21) 2 [0,2,6,8] d21 b2
  have b3 : a 21 ≠ 8 := exclude [0,3] (fun u v => edge r53 v u) (a 21) (a 17) 8 d17 c53 (by decide +kernel)
  have t3 : a 21 ∈ [0,6] := remove (a 21) 8 [0,6,8] t2 b3
  have b4 : a 18 ≠ 2 := exclude [0,3] (edge r55) (a 18) (a 19) 2 d19 c55 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b4
  have b5 : a 22 ≠ 2 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 2 t4 c56 (by decide +kernel)
  have t5 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b5
  have b6 : a 23 ≠ 2 := exclude [0,3] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,3,6,7] := remove (a 23) 2 [0,1,2,3,6,7] d23 b6
  have b7 : a 23 ≠ 3 := exclude [0,3] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,6,7] := remove (a 23) 3 [0,1,3,6,7] t6 b7
  have b8 : a 23 ≠ 7 := exclude [0,3] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,6] := remove (a 23) 7 [0,1,6,7] t7 b8
  have b9 : a 27 ≠ 1 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t9 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d27 b9
  have b10 : a 27 ≠ 2 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 2 d19 c59 (by decide +kernel)
  have t10 : a 27 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 27 ≠ 3 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 3 d19 c59 (by decide +kernel)
  have t11 : a 27 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 27 ≠ 5 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 5 d19 c59 (by decide +kernel)
  have t12 : a 27 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 27 ≠ 6 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 6 d19 c59 (by decide +kernel)
  have t13 : a 27 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 27 ≠ 7 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 7 d19 c59 (by decide +kernel)
  have t14 : a 27 ∈ [0,4,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 27 ≠ 8 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 8 d19 c59 (by decide +kernel)
  have t15 : a 27 ∈ [0,4,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 8 [0,4,8,9,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t8 (t15)))))

theorem chunk13 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,4,9,10,11,12,13,14,15,16,17,18,19])
    (d19 : a 19 ∈ [0,3])
    (d20 : a 20 ∈ [0,1,6,7])
    (d21 : a 21 ∈ [0,6])
    (d29 : a 29 ∈ [0,4,12,16])
    (d23 : a 23 ∈ [0,1,6])
    (d22 : a 22 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d24 : a 24 ∈ [0,2])
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 27 ∈ [0,4,12,16] ∧ a 20 ∈ [0,6] ∧ a 29 ∈ [0,12] ∧ a 23 ∈ [0] ∧ a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 27 ≠ 9 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 9 d19 c59 (by decide +kernel)
  have t0 : a 27 ∈ [0,4,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 9 [0,4,9,10,11,12,13,14,15,16,17,18,19] d27 b0
  have b1 : a 27 ≠ 10 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 10 d19 c59 (by decide +kernel)
  have t1 : a 27 ∈ [0,4,11,12,13,14,15,16,17,18,19] := remove (a 27) 10 [0,4,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 27 ≠ 11 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 11 d19 c59 (by decide +kernel)
  have t2 : a 27 ∈ [0,4,12,13,14,15,16,17,18,19] := remove (a 27) 11 [0,4,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 27 ≠ 13 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 13 d19 c59 (by decide +kernel)
  have t3 : a 27 ∈ [0,4,12,14,15,16,17,18,19] := remove (a 27) 13 [0,4,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 27 ≠ 14 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 14 d19 c59 (by decide +kernel)
  have t4 : a 27 ∈ [0,4,12,15,16,17,18,19] := remove (a 27) 14 [0,4,12,14,15,16,17,18,19] t3 b4
  have b5 : a 27 ≠ 15 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 15 d19 c59 (by decide +kernel)
  have t5 : a 27 ∈ [0,4,12,16,17,18,19] := remove (a 27) 15 [0,4,12,15,16,17,18,19] t4 b5
  have b6 : a 27 ≠ 17 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 17 d19 c59 (by decide +kernel)
  have t6 : a 27 ∈ [0,4,12,16,18,19] := remove (a 27) 17 [0,4,12,16,17,18,19] t5 b6
  have b7 : a 27 ≠ 18 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 18 d19 c59 (by decide +kernel)
  have t7 : a 27 ∈ [0,4,12,16,19] := remove (a 27) 18 [0,4,12,16,18,19] t6 b7
  have b8 : a 27 ≠ 19 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 19 d19 c59 (by decide +kernel)
  have t8 : a 27 ∈ [0,4,12,16] := remove (a 27) 19 [0,4,12,16,19] t7 b8
  have b9 : a 20 ≠ 1 := exclude [0,6] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t9 : a 20 ∈ [0,6,7] := remove (a 20) 1 [0,1,6,7] d20 b9
  have b10 : a 20 ≠ 7 := exclude [0,6] (edge r60) (a 20) (a 21) 7 d21 c60 (by decide +kernel)
  have t10 : a 20 ∈ [0,6] := remove (a 20) 7 [0,6,7] t9 b10
  have b11 : a 29 ≠ 4 := exclude [0,6] (fun u v => edge r64 v u) (a 29) (a 21) 4 d21 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0,12,16] := remove (a 29) 4 [0,4,12,16] d29 b11
  have b12 : a 29 ≠ 16 := exclude [0,6] (fun u v => edge r64 v u) (a 29) (a 21) 16 d21 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,12] := remove (a 29) 16 [0,12,16] t11 b12
  have b13 : a 23 ≠ 1 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 1 d22 c65 (by decide +kernel)
  have t13 : a 23 ∈ [0,6] := remove (a 23) 1 [0,1,6] d23 b13
  have b14 : a 23 ≠ 6 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 6 d22 c65 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 6 [0,6] t13 b14
  have b15 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t15 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d25 b15
  exact And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

theorem chunk14 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d24 : a 24 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,6])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    : a 25 ∈ [0,2,12,14] ∧ a 24 ∈ [0] := by
  have b0 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 3 d24 c68 (by decide +kernel)
  have t0 : a 25 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d25 b0
  have b1 : a 25 ≠ 4 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t1 : a 25 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 5 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 25 ≠ 6 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 6 d24 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 7 d24 c68 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 25 ≠ 8 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 8 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,9,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 8 [0,2,8,9,10,11,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 25 ≠ 9 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 9 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,10,11,12,13,14,15,16,17,18,19] := remove (a 25) 9 [0,2,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 25 ≠ 10 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 10 d24 c68 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,11,12,13,14,15,16,17,18,19] := remove (a 25) 10 [0,2,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 11 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,12,13,14,15,16,17,18,19] := remove (a 25) 11 [0,2,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 25 ≠ 13 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 13 d24 c68 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,12,14,15,16,17,18,19] := remove (a 25) 13 [0,2,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 25 ≠ 15 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 15 d24 c68 (by decide +kernel)
  have t10 : a 25 ∈ [0,2,12,14,16,17,18,19] := remove (a 25) 15 [0,2,12,14,15,16,17,18,19] t9 b10
  have b11 : a 25 ≠ 16 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 16 d24 c68 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,12,14,17,18,19] := remove (a 25) 16 [0,2,12,14,16,17,18,19] t10 b11
  have b12 : a 25 ≠ 17 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 17 d24 c68 (by decide +kernel)
  have t12 : a 25 ∈ [0,2,12,14,18,19] := remove (a 25) 17 [0,2,12,14,17,18,19] t11 b12
  have b13 : a 25 ≠ 18 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 18 d24 c68 (by decide +kernel)
  have t13 : a 25 ∈ [0,2,12,14,19] := remove (a 25) 18 [0,2,12,14,18,19] t12 b13
  have b14 : a 25 ≠ 19 := exclude [0,2] (fun u v => edge r68 v u) (a 25) (a 24) 19 d24 c68 (by decide +kernel)
  have t14 : a 25 ∈ [0,2,12,14] := remove (a 25) 19 [0,2,12,14,19] t13 b14
  have b15 : a 24 ≠ 2 := exclude [0,1,6] (edge r70) (a 24) (a 28) 2 d28 c70 (by decide +kernel)
  have t15 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b15
  exact And.intro t14 (t15)

theorem chunk15 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,6])
    (d24 : a 24 ∈ [0])
    (d25 : a 25 ∈ [0,2,12,14])
    (d27 : a 27 ∈ [0,4,12,16])
    (d7 : a 7 ∈ [0,1,4,5])
    (d15 : a 15 ∈ [0,8])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    : a 28 ∈ [0] ∧ a 25 ∈ [0,12] ∧ a 27 ∈ [0,12] ∧ a 7 ∈ [0,4] := by
  have b0 : a 28 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 1 d24 c70 (by decide +kernel)
  have t0 : a 28 ∈ [0,6] := remove (a 28) 1 [0,1,6] d28 b0
  have b1 : a 28 ≠ 6 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 6 d24 c70 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 6 [0,6] t0 b1
  have b2 : a 25 ≠ 2 := exclude [0,4,12,16] (edge r71) (a 25) (a 27) 2 d27 c71 (by decide +kernel)
  have t2 : a 25 ∈ [0,12,14] := remove (a 25) 2 [0,2,12,14] d25 b2
  have b3 : a 25 ≠ 14 := exclude [0,4,12,16] (edge r71) (a 25) (a 27) 14 d27 c71 (by decide +kernel)
  have t3 : a 25 ∈ [0,12] := remove (a 25) 14 [0,12,14] t2 b3
  have b4 : a 27 ≠ 4 := exclude [0,12] (fun u v => edge r71 v u) (a 27) (a 25) 4 t3 c71 (by decide +kernel)
  have t4 : a 27 ∈ [0,12,16] := remove (a 27) 4 [0,4,12,16] d27 b4
  have b5 : a 27 ≠ 16 := exclude [0,12] (fun u v => edge r71 v u) (a 27) (a 25) 16 t3 c71 (by decide +kernel)
  have t5 : a 27 ∈ [0,12] := remove (a 27) 16 [0,12,16] t4 b5
  have b6 : a 7 ≠ 1 := exclude [0,8] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t6 : a 7 ∈ [0,4,5] := remove (a 7) 1 [0,1,4,5] d7 b6
  have b7 : a 7 ≠ 5 := exclude [0,8] (edge r26) (a 7) (a 15) 5 d15 c26 (by decide +kernel)
  have t7 : a 7 ∈ [0,4] := remove (a 7) 5 [0,4,5] t6 b7
  exact And.intro t1 (And.intro t3 (And.intro t5 (t7)))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_208
