import PartitionData205_217
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk28 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,9,10,11])
    (d15 : a 15 ∈ [0])
    (d17 : a 17 ∈ [0,1,10,11,12,13,16,17])
    (d16 : a 16 ∈ [0,11])
    (d18 : a 18 ∈ [0,2,7])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0,1,2,3,4,6,8,9,11])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 31 ∈ [0,1] ∧ a 17 ∈ [0,1,10,11] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 20 ∈ [0,1] ∧ a 19 ∈ [0,2,3,6,8,9,11] := by
  have b0 : a 31 ≠ 9 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,10,11] := remove (a 31) 9 [0,1,9,10,11] d31 b0
  have b1 : a 31 ≠ 10 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,11] := remove (a 31) 10 [0,1,10,11] t0 b1
  have b2 : a 31 ≠ 11 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1] := remove (a 31) 11 [0,1,11] t1 b2
  have b3 : a 17 ≠ 12 := exclude [0,11] (fun u v => edge r48 v u) (a 17) (a 16) 12 d16 c48 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,10,11,13,16,17] := remove (a 17) 12 [0,1,10,11,12,13,16,17] d17 b3
  have b4 : a 17 ≠ 13 := exclude [0,11] (fun u v => edge r48 v u) (a 17) (a 16) 13 d16 c48 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,10,11,16,17] := remove (a 17) 13 [0,1,10,11,13,16,17] t3 b4
  have b5 : a 17 ≠ 16 := exclude [0,11] (fun u v => edge r48 v u) (a 17) (a 16) 16 d16 c48 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,10,11,17] := remove (a 17) 16 [0,1,10,11,16,17] t4 b5
  have b6 : a 17 ≠ 17 := exclude [0,11] (fun u v => edge r48 v u) (a 17) (a 16) 17 d16 c48 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,10,11] := remove (a 17) 17 [0,1,10,11,17] t5 b6
  have b7 : a 16 ≠ 11 := exclude [0,2,7] (edge r49) (a 16) (a 18) 11 d18 c49 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 11 [0,11] d16 b7
  have b8 : a 18 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 2 t7 c49 (by decide +kernel)
  have t8 : a 18 ∈ [0,7] := remove (a 18) 2 [0,2,7] d18 b8
  have b9 : a 18 ≠ 7 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 7 t7 c49 (by decide +kernel)
  have t9 : a 18 ∈ [0] := remove (a 18) 7 [0,7] t8 b9
  have b10 : a 20 ≠ 2 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 2 t7 c50 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,3,4,5] := remove (a 20) 2 [0,1,2,3,4,5] d20 b10
  have b11 : a 20 ≠ 3 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 3 t7 c50 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,4,5] := remove (a 20) 3 [0,1,3,4,5] t10 b11
  have b12 : a 20 ≠ 4 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 4 t7 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,5] := remove (a 20) 4 [0,1,4,5] t11 b12
  have b13 : a 20 ≠ 5 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 5 t7 c50 (by decide +kernel)
  have t13 : a 20 ∈ [0,1] := remove (a 20) 5 [0,1,5] t12 b13
  have b14 : a 19 ≠ 1 := exclude [0,1,10,11] (fun u v => edge r52 v u) (a 19) (a 17) 1 t6 c52 (by decide +kernel)
  have t14 : a 19 ∈ [0,2,3,4,6,8,9,11] := remove (a 19) 1 [0,1,2,3,4,6,8,9,11] d19 b14
  have b15 : a 19 ≠ 4 := exclude [0,1,10,11] (fun u v => edge r52 v u) (a 19) (a 17) 4 t6 c52 (by decide +kernel)
  have t15 : a 19 ∈ [0,2,3,6,8,9,11] := remove (a 19) 4 [0,2,3,4,6,8,9,11] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk29 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,2,3,6,8,9,11])
    (d17 : a 17 ∈ [0,1,10,11])
    (d25 : a 25 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d26 : a 26 ∈ [0,7])
    (d21 : a 21 ∈ [0,8])
    (d20 : a 20 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d23 : a 23 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d24 : a 24 ∈ [0,5,6,11,12,17,18,23])
    (c52 : edge r52 (a 17) (a 19)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 19 ∈ [0,2,6,8] ∧ a 17 ∈ [0,1] ∧ a 26 ∈ [0] ∧ a 21 ∈ [0] ∧ a 20 ∈ [0] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0] ∧ a 31 ∈ [0] ∧ a 24 ∈ [0,6,23] := by
  have b0 : a 19 ≠ 9 := exclude [0,1,10,11] (fun u v => edge r52 v u) (a 19) (a 17) 9 d17 c52 (by decide +kernel)
  have t0 : a 19 ∈ [0,2,3,6,8,11] := remove (a 19) 9 [0,2,3,6,8,9,11] d19 b0
  have b1 : a 17 ≠ 10 := exclude [0,1] (edge r54) (a 17) (a 25) 10 d25 c54 (by decide +kernel)
  have t1 : a 17 ∈ [0,1,11] := remove (a 17) 10 [0,1,10,11] d17 b1
  have b2 : a 17 ≠ 11 := exclude [0,1] (edge r54) (a 17) (a 25) 11 d25 c54 (by decide +kernel)
  have t2 : a 17 ∈ [0,1] := remove (a 17) 11 [0,1,11] t1 b2
  have b3 : a 19 ≠ 3 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,2,6,8,11] := remove (a 19) 3 [0,2,3,6,8,11] t0 b3
  have b4 : a 19 ≠ 11 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 11 d18 c55 (by decide +kernel)
  have t4 : a 19 ∈ [0,2,6,8] := remove (a 19) 11 [0,2,6,8,11] t3 b4
  have b5 : a 26 ≠ 7 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 7 d18 c57 (by decide +kernel)
  have t5 : a 26 ∈ [0] := remove (a 26) 7 [0,7] d26 b5
  have b6 : a 21 ≠ 8 := exclude [0,1] (fun u v => edge r60 v u) (a 21) (a 20) 8 d20 c60 (by decide +kernel)
  have t6 : a 21 ∈ [0] := remove (a 21) 8 [0,8] d21 b6
  have b7 : a 20 ≠ 1 := exclude [0,2] (edge r61) (a 20) (a 22) 1 d22 c61 (by decide +kernel)
  have t7 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b7
  have b8 : a 22 ≠ 2 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 2 t7 c61 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b8
  have b9 : a 23 ≠ 2 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 2 t6 c63 (by decide +kernel)
  have t9 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b9
  have b10 : a 31 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 1 t9 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b10
  have b11 : a 24 ≠ 5 := exclude [0,1] (edge r68) (a 24) (a 25) 5 d25 c68 (by decide +kernel)
  have t11 : a 24 ∈ [0,6,11,12,17,18,23] := remove (a 24) 5 [0,5,6,11,12,17,18,23] d24 b11
  have b12 : a 24 ≠ 11 := exclude [0,1] (edge r68) (a 24) (a 25) 11 d25 c68 (by decide +kernel)
  have t12 : a 24 ∈ [0,6,12,17,18,23] := remove (a 24) 11 [0,6,11,12,17,18,23] t11 b12
  have b13 : a 24 ≠ 12 := exclude [0,1] (edge r68) (a 24) (a 25) 12 d25 c68 (by decide +kernel)
  have t13 : a 24 ∈ [0,6,17,18,23] := remove (a 24) 12 [0,6,12,17,18,23] t12 b13
  have b14 : a 24 ≠ 17 := exclude [0,1] (edge r68) (a 24) (a 25) 17 d25 c68 (by decide +kernel)
  have t14 : a 24 ∈ [0,6,18,23] := remove (a 24) 17 [0,6,17,18,23] t13 b14
  have b15 : a 24 ≠ 18 := exclude [0,1] (edge r68) (a 24) (a 25) 18 d25 c68 (by decide +kernel)
  have t15 : a 24 ∈ [0,6,23] := remove (a 24) 18 [0,6,18,23] t14 b15
  exact And.intro t4 (And.intro t2 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t15))))))))

theorem chunk30 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6,23])
    (d25 : a 25 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d27 : a 27 ∈ [0,7,9])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d28 : a 28 ∈ [0,8])
    (d29 : a 29 ∈ [0,1])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 27 ∈ [0] ∧ a 30 ∈ [0,1] ∧ a 28 ∈ [0] := by
  have b0 : a 24 ≠ 23 := exclude [0,1] (edge r68) (a 24) (a 25) 23 d25 c68 (by decide +kernel)
  have t0 : a 24 ∈ [0,6] := remove (a 24) 23 [0,6,23] d24 b0
  have b1 : a 24 ≠ 6 := exclude [0] (edge r69) (a 24) (a 26) 6 d26 c69 (by decide +kernel)
  have t1 : a 24 ∈ [0] := remove (a 24) 6 [0,6] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0,7,9] (edge r71) (a 25) (a 27) 1 d27 c71 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b2
  have b3 : a 27 ≠ 7 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 7 t2 c71 (by decide +kernel)
  have t3 : a 27 ∈ [0,9] := remove (a 27) 7 [0,7,9] d27 b3
  have b4 : a 27 ≠ 9 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 9 t2 c71 (by decide +kernel)
  have t4 : a 27 ∈ [0] := remove (a 27) 9 [0,9] t3 b4
  have b5 : a 30 ≠ 2 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 2 d26 c74 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b5
  have b6 : a 30 ≠ 3 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 3 d26 c74 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 30 ≠ 4 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 4 d26 c74 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 30) 4 [0,1,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 30 ≠ 5 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 5 d26 c74 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,6,7,8,9,10,11] := remove (a 30) 5 [0,1,5,6,7,8,9,10,11] t7 b8
  have b9 : a 30 ≠ 6 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 6 d26 c74 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,7,8,9,10,11] := remove (a 30) 6 [0,1,6,7,8,9,10,11] t8 b9
  have b10 : a 30 ≠ 7 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 7 d26 c74 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,8,9,10,11] := remove (a 30) 7 [0,1,7,8,9,10,11] t9 b10
  have b11 : a 30 ≠ 8 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 8 d26 c74 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,9,10,11] := remove (a 30) 8 [0,1,8,9,10,11] t10 b11
  have b12 : a 30 ≠ 9 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 9 d26 c74 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,10,11] := remove (a 30) 9 [0,1,9,10,11] t11 b12
  have b13 : a 30 ≠ 10 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 10 d26 c74 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,11] := remove (a 30) 10 [0,1,10,11] t12 b13
  have b14 : a 30 ≠ 11 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 11 d26 c74 (by decide +kernel)
  have t14 : a 30 ∈ [0,1] := remove (a 30) 11 [0,1,11] t13 b14
  have b15 : a 28 ≠ 8 := exclude [0,1] (edge r76) (a 28) (a 29) 8 d29 c76 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 8 [0,8] d28 b15
  exact And.intro t1 (And.intro t2 (And.intro t4 (And.intro t14 (t15))))

theorem chunk31 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d1 : a 1 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1])
    (d5 : a 5 ∈ [0,2])
    (d7 : a 7 ∈ [0,2])
    (d4 : a 4 ∈ [0,6])
    (d6 : a 6 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d23 : a 23 ∈ [0])
    (d19 : a 19 ∈ [0,2,6,8])
    (d17 : a 17 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 1 ∈ [0] ∧ a 3 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 19 ∈ [0] ∧ a 5 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 29 ≠ 1 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 1 d28 c76 (by decide +kernel)
  have t0 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b0
  have b1 : a 30 ≠ 1 := exclude [0] (fun u v => edge r77 v u) (a 30) (a 28) 1 d28 c77 (by decide +kernel)
  have t1 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b1
  have b2 : a 1 ≠ 2 := exclude [0,1] (edge r5) (a 1) (a 3) 2 d3 c5 (by decide +kernel)
  have t2 : a 1 ∈ [0,1] := remove (a 1) 2 [0,1,2] d1 b2
  have b3 : a 1 ≠ 1 := exclude [0,2] (edge r6) (a 1) (a 5) 1 d5 c6 (by decide +kernel)
  have t3 : a 1 ∈ [0] := remove (a 1) 1 [0,1] t2 b3
  have b4 : a 3 ≠ 1 := exclude [0,2] (edge r13) (a 3) (a 7) 1 d7 c13 (by decide +kernel)
  have t4 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b4
  have b5 : a 4 ≠ 6 := exclude [0,2] (edge r16) (a 4) (a 5) 6 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 6 [0,6] d4 b5
  have b6 : a 6 ≠ 2 := exclude [0] (edge r24) (a 6) (a 14) 2 d14 c24 (by decide +kernel)
  have t6 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b6
  have b7 : a 7 ≠ 2 := exclude [0] (edge r27) (a 7) (a 23) 2 d23 c27 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b7
  have b8 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 2 d17 c52 (by decide +kernel)
  have t8 : a 19 ∈ [0,6,8] := remove (a 19) 2 [0,2,6,8] d19 b8
  have b9 : a 19 ≠ 8 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 8 d17 c52 (by decide +kernel)
  have t9 : a 19 ∈ [0,6] := remove (a 19) 8 [0,6,8] t8 b9
  have b10 : a 19 ≠ 6 := exclude [0] (edge r58) (a 19) (a 23) 6 d23 c58 (by decide +kernel)
  have t10 : a 19 ∈ [0] := remove (a 19) 6 [0,6] t9 b10
  have b11 : a 5 ≠ 2 := exclude [0] (edge r20) (a 5) (a 7) 2 t7 c20 (by decide +kernel)
  have t11 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b11
  have b12 : a 17 ≠ 1 := exclude [0] (edge r52) (a 17) (a 19) 1 t10 c52 (by decide +kernel)
  have t12 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b12
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t10 (And.intro t11 (t12)))))))))
#print axioms chunk28
#print axioms chunk29
#print axioms chunk30
#print axioms chunk31
end PartitionCover205_217
