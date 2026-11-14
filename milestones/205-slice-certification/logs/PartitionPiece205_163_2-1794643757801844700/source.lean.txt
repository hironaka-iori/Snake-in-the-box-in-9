import PartitionData205_163
namespace PartitionCover205_163
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,5,6,7,8,9])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0])
    (d18 : a 18 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1,2])
    (d25 : a 25 ∈ [0,1,4])
    (d26 : a 26 ∈ [0,6])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 31 ∈ [0,1,2,3] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3,6,7,8,9] := remove (a 31) 5 [0,1,2,3,5,6,7,8,9] d31 b0
  have b1 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,2,3,7,8,9] := remove (a 31) 6 [0,1,2,3,6,7,8,9] t0 b1
  have b2 : a 31 ≠ 7 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,2,3,8,9] := remove (a 31) 7 [0,1,2,3,7,8,9] t1 b2
  have b3 : a 31 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,2,3,9] := remove (a 31) 8 [0,1,2,3,8,9] t2 b3
  have b4 : a 31 ≠ 9 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,2,3] := remove (a 31) 9 [0,1,2,3,9] t3 b4
  have b5 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 17) 1 d17 c48 (by decide +kernel)
  have t5 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b5
  have b6 : a 16 ≠ 2 := exclude [0] (edge r48) (a 16) (a 17) 2 d17 c48 (by decide +kernel)
  have t6 : a 16 ∈ [0,3] := remove (a 16) 2 [0,2,3] t5 b6
  have b7 : a 16 ≠ 3 := exclude [0] (edge r48) (a 16) (a 17) 3 d17 c48 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 3 [0,3] t6 b7
  have b8 : a 18 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 1 t7 c49 (by decide +kernel)
  have t8 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b8
  have b9 : a 18 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 2 t7 c49 (by decide +kernel)
  have t9 : a 18 ∈ [0,3] := remove (a 18) 2 [0,2,3] t8 b9
  have b10 : a 18 ≠ 3 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 3 t7 c49 (by decide +kernel)
  have t10 : a 18 ∈ [0] := remove (a 18) 3 [0,3] t9 b10
  have b11 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t11 : a 19 ∈ [0,2] := remove (a 19) 1 [0,1,2] d19 b11
  have b12 : a 19 ≠ 2 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 2 d17 c52 (by decide +kernel)
  have t12 : a 19 ∈ [0] := remove (a 19) 2 [0,2] t11 b12
  have b13 : a 25 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 1 d17 c54 (by decide +kernel)
  have t13 : a 25 ∈ [0,4] := remove (a 25) 1 [0,1,4] d25 b13
  have b14 : a 25 ≠ 4 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 4 d17 c54 (by decide +kernel)
  have t14 : a 25 ∈ [0] := remove (a 25) 4 [0,4] t13 b14
  have b15 : a 26 ≠ 6 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 6 t10 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 6 [0,6] d26 b15
  exact And.intro t4 (And.intro t7 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))

theorem chunk9 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7])
    (d19 : a 19 ∈ [0])
    (d27 : a 27 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,4,5,10,11])
    (d22 : a 22 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d21 : a 21 ∈ [0])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    : a 23 ∈ [0,2] ∧ a 27 ∈ [0] ∧ a 20 ∈ [0,1] ∧ a 22 ∈ [0,2] ∧ a 29 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 23 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,2,3,4,5,6,7] := remove (a 23) 1 [0,1,2,3,4,5,6,7] d23 b0
  have b1 : a 23 ≠ 3 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,2,4,5,6,7] := remove (a 23) 3 [0,2,3,4,5,6,7] t0 b1
  have b2 : a 23 ≠ 4 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,2,5,6,7] := remove (a 23) 4 [0,2,4,5,6,7] t1 b2
  have b3 : a 23 ≠ 5 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,2,6,7] := remove (a 23) 5 [0,2,5,6,7] t2 b3
  have b4 : a 23 ≠ 6 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 6 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,2,7] := remove (a 23) 6 [0,2,6,7] t3 b4
  have b5 : a 23 ≠ 7 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,2] := remove (a 23) 7 [0,2,7] t4 b5
  have b6 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t6 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b6
  have b7 : a 20 ≠ 10 := exclude [0,1,2,3] (edge r61) (a 20) (a 22) 10 d22 c61 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,4,5,11] := remove (a 20) 10 [0,1,4,5,10,11] d20 b7
  have b8 : a 20 ≠ 11 := exclude [0,1,2,3] (edge r61) (a 20) (a 22) 11 d22 c61 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,4,5] := remove (a 20) 11 [0,1,4,5,11] t7 b8
  have b9 : a 22 ≠ 1 := exclude [0,1,4,5] (fun u v => edge r61 v u) (a 22) (a 20) 1 t8 c61 (by decide +kernel)
  have t9 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b9
  have b10 : a 22 ≠ 3 := exclude [0,1,4,5] (fun u v => edge r61 v u) (a 22) (a 20) 3 t8 c61 (by decide +kernel)
  have t10 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t9 b10
  have b11 : a 20 ≠ 4 := exclude [0,1] (edge r62) (a 20) (a 28) 4 d28 c62 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,5] := remove (a 20) 4 [0,1,4,5] t8 b11
  have b12 : a 20 ≠ 5 := exclude [0,1] (edge r62) (a 20) (a 28) 5 d28 c62 (by decide +kernel)
  have t12 : a 20 ∈ [0,1] := remove (a 20) 5 [0,1,5] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 3 d21 c64 (by decide +kernel)
  have t14 : a 29 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 29 ≠ 5 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 5 d21 c64 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 5 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t5 (And.intro t6 (And.intro t12 (And.intro t10 (t15))))

theorem chunk10 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d21 : a 21 ∈ [0])
    (d22 : a 22 ∈ [0,2])
    (d23 : a 23 ∈ [0,2])
    (d30 : a 30 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3])
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 29 ∈ [0,2,4,6] ∧ a 22 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0,1,3] := by
  have b0 : a 29 ≠ 7 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 7 d21 c64 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 7 [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d29 b0
  have b1 : a 29 ≠ 8 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 8 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0,2,4,6,9,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 8 [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 29 ≠ 9 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 9 d21 c64 (by decide +kernel)
  have t2 : a 29 ∈ [0,2,4,6,10,11,12,13,14,15,16,17,18,19] := remove (a 29) 9 [0,2,4,6,9,10,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 29 ≠ 10 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 10 d21 c64 (by decide +kernel)
  have t3 : a 29 ∈ [0,2,4,6,11,12,13,14,15,16,17,18,19] := remove (a 29) 10 [0,2,4,6,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 29 ≠ 11 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 11 d21 c64 (by decide +kernel)
  have t4 : a 29 ∈ [0,2,4,6,12,13,14,15,16,17,18,19] := remove (a 29) 11 [0,2,4,6,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 29 ≠ 12 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 12 d21 c64 (by decide +kernel)
  have t5 : a 29 ∈ [0,2,4,6,13,14,15,16,17,18,19] := remove (a 29) 12 [0,2,4,6,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 29 ≠ 13 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 13 d21 c64 (by decide +kernel)
  have t6 : a 29 ∈ [0,2,4,6,14,15,16,17,18,19] := remove (a 29) 13 [0,2,4,6,13,14,15,16,17,18,19] t5 b6
  have b7 : a 29 ≠ 14 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 14 d21 c64 (by decide +kernel)
  have t7 : a 29 ∈ [0,2,4,6,15,16,17,18,19] := remove (a 29) 14 [0,2,4,6,14,15,16,17,18,19] t6 b7
  have b8 : a 29 ≠ 15 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 15 d21 c64 (by decide +kernel)
  have t8 : a 29 ∈ [0,2,4,6,16,17,18,19] := remove (a 29) 15 [0,2,4,6,15,16,17,18,19] t7 b8
  have b9 : a 29 ≠ 16 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 16 d21 c64 (by decide +kernel)
  have t9 : a 29 ∈ [0,2,4,6,17,18,19] := remove (a 29) 16 [0,2,4,6,16,17,18,19] t8 b9
  have b10 : a 29 ≠ 17 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 17 d21 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0,2,4,6,18,19] := remove (a 29) 17 [0,2,4,6,17,18,19] t9 b10
  have b11 : a 29 ≠ 18 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 18 d21 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0,2,4,6,19] := remove (a 29) 18 [0,2,4,6,18,19] t10 b11
  have b12 : a 29 ≠ 19 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 19 d21 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,2,4,6] := remove (a 29) 19 [0,2,4,6,19] t11 b12
  have b13 : a 22 ≠ 2 := exclude [0,2] (edge r65) (a 22) (a 23) 2 d23 c65 (by decide +kernel)
  have t13 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b13
  have b14 : a 30 ≠ 2 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 2 t13 c66 (by decide +kernel)
  have t14 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b14
  have b15 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b15
  exact And.intro t12 (And.intro t13 (And.intro t14 (t15)))

theorem chunk11 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,3])
    (d23 : a 23 ∈ [0,2])
    (d24 : a 24 ∈ [0,4,10])
    (d25 : a 25 ∈ [0])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,2,4,6])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 31 ∈ [0] ∧ a 24 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 5 ∈ [0] ∧ a 20 ∈ [0] ∧ a 23 ∈ [0] := by
  have b0 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 3 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] d31 b0
  have b1 : a 24 ≠ 4 := exclude [0] (edge r68) (a 24) (a 25) 4 d25 c68 (by decide +kernel)
  have t1 : a 24 ∈ [0,10] := remove (a 24) 4 [0,4,10] d24 b1
  have b2 : a 24 ≠ 10 := exclude [0] (edge r68) (a 24) (a 25) 10 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 10 [0,10] t1 b2
  have b3 : a 28 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 1 t2 c70 (by decide +kernel)
  have t3 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b3
  have b4 : a 29 ≠ 2 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 2 t3 c76 (by decide +kernel)
  have t4 : a 29 ∈ [0,4,6] := remove (a 29) 2 [0,2,4,6] d29 b4
  have b5 : a 29 ≠ 4 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 4 t3 c76 (by decide +kernel)
  have t5 : a 29 ∈ [0,6] := remove (a 29) 4 [0,4,6] t4 b5
  have b6 : a 29 ≠ 6 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 6 t3 c76 (by decide +kernel)
  have t6 : a 29 ∈ [0] := remove (a 29) 6 [0,6] t5 b6
  have b7 : a 31 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 31) (a 29) 1 t6 c78 (by decide +kernel)
  have t7 : a 31 ∈ [0] := remove (a 31) 1 [0,1] t0 b7
  have b8 : a 5 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t8 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b8
  have b9 : a 20 ≠ 1 := exclude [0] (edge r62) (a 20) (a 28) 1 t3 c62 (by decide +kernel)
  have t9 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b9
  have b10 : a 23 ≠ 2 := exclude [0] (edge r67) (a 23) (a 31) 2 t7 c67 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b10
  exact And.intro t7 (And.intro t2 (And.intro t3 (And.intro t6 (And.intro t8 (And.intro t9 (t10))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_163
