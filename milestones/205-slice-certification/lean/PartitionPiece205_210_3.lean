import PartitionData205_210
namespace PartitionCover205_210
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,3,4,5,7,9,10,11])
    (d18 : a 18 ∈ [0,6,10,12])
    (d26 : a 26 ∈ [0,2,3,5,8,11])
    (d19 : a 19 ∈ [0,3,5,6])
    (d23 : a 23 ∈ [0,1,4,5])
    (d29 : a 29 ∈ [0,1,4,5,7,8])
    (d21 : a 21 ∈ [0,2])
    (d30 : a 30 ∈ [0,1,3,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22])
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 22 ∈ [0,2,7,9] ∧ a 26 ∈ [0,2,3,8] ∧ a 19 ∈ [0,6] ∧ a 23 ∈ [0,4] ∧ a 29 ∈ [0,1,4,5] ∧ a 30 ∈ [0,1,4,6,7,9,10,11,12,13,14,16,19,20,21,22] := by
  have b0 : a 22 ≠ 1 := exclude [0,6,10,12] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t0 : a 22 ∈ [0,2,3,4,5,7,9,10,11] := remove (a 22) 1 [0,1,2,3,4,5,7,9,10,11] d22 b0
  have b1 : a 22 ≠ 3 := exclude [0,6,10,12] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,4,5,7,9,10,11] := remove (a 22) 3 [0,2,3,4,5,7,9,10,11] t0 b1
  have b2 : a 22 ≠ 4 := exclude [0,6,10,12] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t2 : a 22 ∈ [0,2,5,7,9,10,11] := remove (a 22) 4 [0,2,4,5,7,9,10,11] t1 b2
  have b3 : a 22 ≠ 5 := exclude [0,6,10,12] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t3 : a 22 ∈ [0,2,7,9,10,11] := remove (a 22) 5 [0,2,5,7,9,10,11] t2 b3
  have b4 : a 22 ≠ 10 := exclude [0,6,10,12] (fun u v => edge r56 v u) (a 22) (a 18) 10 d18 c56 (by decide +kernel)
  have t4 : a 22 ∈ [0,2,7,9,11] := remove (a 22) 10 [0,2,7,9,10,11] t3 b4
  have b5 : a 22 ≠ 11 := exclude [0,6,10,12] (fun u v => edge r56 v u) (a 22) (a 18) 11 d18 c56 (by decide +kernel)
  have t5 : a 22 ∈ [0,2,7,9] := remove (a 22) 11 [0,2,7,9,11] t4 b5
  have b6 : a 26 ≠ 5 := exclude [0,6,10,12] (fun u v => edge r57 v u) (a 26) (a 18) 5 d18 c57 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,3,8,11] := remove (a 26) 5 [0,2,3,5,8,11] d26 b6
  have b7 : a 26 ≠ 11 := exclude [0,6,10,12] (fun u v => edge r57 v u) (a 26) (a 18) 11 d18 c57 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,3,8] := remove (a 26) 11 [0,2,3,8,11] t6 b7
  have b8 : a 19 ≠ 3 := exclude [0,1,4,5] (edge r58) (a 19) (a 23) 3 d23 c58 (by decide +kernel)
  have t8 : a 19 ∈ [0,5,6] := remove (a 19) 3 [0,3,5,6] d19 b8
  have b9 : a 19 ≠ 5 := exclude [0,1,4,5] (edge r58) (a 19) (a 23) 5 d23 c58 (by decide +kernel)
  have t9 : a 19 ∈ [0,6] := remove (a 19) 5 [0,5,6] t8 b9
  have b10 : a 23 ≠ 1 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 1 t9 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,4,5] := remove (a 23) 1 [0,1,4,5] d23 b10
  have b11 : a 23 ≠ 5 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 5 t9 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,4] := remove (a 23) 5 [0,4,5] t10 b11
  have b12 : a 29 ≠ 7 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 7 d21 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,4,5,8] := remove (a 29) 7 [0,1,4,5,7,8] d29 b12
  have b13 : a 29 ≠ 8 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 8 d21 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,4,5] := remove (a 29) 8 [0,1,4,5,8] t12 b13
  have b14 : a 30 ≠ 3 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 3 t5 c66 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22] := remove (a 30) 3 [0,1,3,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22] d30 b14
  have b15 : a 30 ≠ 5 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 5 t5 c66 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,4,6,7,9,10,11,12,13,14,16,19,20,21,22] := remove (a 30) 5 [0,1,4,5,6,7,9,10,11,12,13,14,16,19,20,21,22] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t13 (t15)))))

theorem chunk13 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,4,6,7,9,10,11,12,13,14,16,19,20,21,22])
    (d22 : a 22 ∈ [0,2,7,9])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7])
    (d23 : a 23 ∈ [0,4])
    (d26 : a 26 ∈ [0,2,3,8])
    (d24 : a 24 ∈ [0,8])
    (d27 : a 27 ∈ [0,1,4])
    (d25 : a 25 ∈ [0,8])
    (d29 : a 29 ∈ [0,1,4,5])
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 30 ∈ [0,1,4,6,10,12,20,21] ∧ a 31 ∈ [0,3,4,7] ∧ a 26 ∈ [0,8] ∧ a 27 ∈ [0,4] ∧ a 29 ∈ [0,4,5] := by
  have b0 : a 30 ≠ 7 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 7 d22 c66 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,4,6,9,10,11,12,13,14,16,19,20,21,22] := remove (a 30) 7 [0,1,4,6,7,9,10,11,12,13,14,16,19,20,21,22] d30 b0
  have b1 : a 30 ≠ 9 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 9 d22 c66 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,4,6,10,11,12,13,14,16,19,20,21,22] := remove (a 30) 9 [0,1,4,6,9,10,11,12,13,14,16,19,20,21,22] t0 b1
  have b2 : a 30 ≠ 11 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 11 d22 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,4,6,10,12,13,14,16,19,20,21,22] := remove (a 30) 11 [0,1,4,6,10,11,12,13,14,16,19,20,21,22] t1 b2
  have b3 : a 30 ≠ 13 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 13 d22 c66 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,4,6,10,12,14,16,19,20,21,22] := remove (a 30) 13 [0,1,4,6,10,12,13,14,16,19,20,21,22] t2 b3
  have b4 : a 30 ≠ 14 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 14 d22 c66 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,4,6,10,12,16,19,20,21,22] := remove (a 30) 14 [0,1,4,6,10,12,14,16,19,20,21,22] t3 b4
  have b5 : a 30 ≠ 16 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 16 d22 c66 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,4,6,10,12,19,20,21,22] := remove (a 30) 16 [0,1,4,6,10,12,16,19,20,21,22] t4 b5
  have b6 : a 30 ≠ 19 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 19 d22 c66 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,4,6,10,12,20,21,22] := remove (a 30) 19 [0,1,4,6,10,12,19,20,21,22] t5 b6
  have b7 : a 30 ≠ 22 := exclude [0,2,7,9] (fun u v => edge r66 v u) (a 30) (a 22) 22 d22 c66 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,4,6,10,12,20,21] := remove (a 30) 22 [0,1,4,6,10,12,20,21,22] t6 b7
  have b8 : a 31 ≠ 1 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 1 d23 c67 (by decide +kernel)
  have t8 : a 31 ∈ [0,2,3,4,5,6,7] := remove (a 31) 1 [0,1,2,3,4,5,6,7] d31 b8
  have b9 : a 31 ≠ 2 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t9 : a 31 ∈ [0,3,4,5,6,7] := remove (a 31) 2 [0,2,3,4,5,6,7] t8 b9
  have b10 : a 31 ≠ 5 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0,3,4,6,7] := remove (a 31) 5 [0,3,4,5,6,7] t9 b10
  have b11 : a 31 ≠ 6 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 6 d23 c67 (by decide +kernel)
  have t11 : a 31 ∈ [0,3,4,7] := remove (a 31) 6 [0,3,4,6,7] t10 b11
  have b12 : a 26 ≠ 2 := exclude [0,8] (fun u v => edge r69 v u) (a 26) (a 24) 2 d24 c69 (by decide +kernel)
  have t12 : a 26 ∈ [0,3,8] := remove (a 26) 2 [0,2,3,8] d26 b12
  have b13 : a 26 ≠ 3 := exclude [0,8] (fun u v => edge r69 v u) (a 26) (a 24) 3 d24 c69 (by decide +kernel)
  have t13 : a 26 ∈ [0,8] := remove (a 26) 3 [0,3,8] t12 b13
  have b14 : a 27 ≠ 1 := exclude [0,8] (fun u v => edge r71 v u) (a 27) (a 25) 1 d25 c71 (by decide +kernel)
  have t14 : a 27 ∈ [0,4] := remove (a 27) 1 [0,1,4] d27 b14
  have b15 : a 29 ≠ 1 := exclude [0,8] (fun u v => edge r72 v u) (a 29) (a 25) 1 d25 c72 (by decide +kernel)
  have t15 : a 29 ∈ [0,4,5] := remove (a 29) 1 [0,1,4,5] d29 b15
  exact And.intro t7 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))

theorem chunk14 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,4,5])
    (d25 : a 25 ∈ [0,8])
    (d31 : a 31 ∈ [0,3,4,7])
    (d27 : a 27 ∈ [0,4])
    (d28 : a 28 ∈ [0,10,12,14])
    (d30 : a 30 ∈ [0,1,4,6,10,12,20,21])
    (d4 : a 4 ∈ [0,2,6,8])
    (d12 : a 12 ∈ [0,12])
    (d6 : a 6 ∈ [0,1,4,5])
    (d22 : a 22 ∈ [0,2,7,9])
    (d14 : a 14 ∈ [0,1,12,13])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 29 ∈ [0,4] ∧ a 31 ∈ [0,4] ∧ a 28 ∈ [0,14] ∧ a 30 ∈ [0,1] ∧ a 4 ∈ [0,6] ∧ a 6 ∈ [0,4] ∧ a 14 ∈ [0,12,13] := by
  have b0 : a 29 ≠ 5 := exclude [0,8] (fun u v => edge r72 v u) (a 29) (a 25) 5 d25 c72 (by decide +kernel)
  have t0 : a 29 ∈ [0,4] := remove (a 29) 5 [0,4,5] d29 b0
  have b1 : a 31 ≠ 3 := exclude [0,4] (fun u v => edge r75 v u) (a 31) (a 27) 3 d27 c75 (by decide +kernel)
  have t1 : a 31 ∈ [0,4,7] := remove (a 31) 3 [0,3,4,7] d31 b1
  have b2 : a 31 ≠ 7 := exclude [0,4] (fun u v => edge r75 v u) (a 31) (a 27) 7 d27 c75 (by decide +kernel)
  have t2 : a 31 ∈ [0,4] := remove (a 31) 7 [0,4,7] t1 b2
  have b3 : a 28 ≠ 10 := exclude [0,4] (edge r76) (a 28) (a 29) 10 t0 c76 (by decide +kernel)
  have t3 : a 28 ∈ [0,12,14] := remove (a 28) 10 [0,10,12,14] d28 b3
  have b4 : a 28 ≠ 12 := exclude [0,4] (edge r76) (a 28) (a 29) 12 t0 c76 (by decide +kernel)
  have t4 : a 28 ∈ [0,14] := remove (a 28) 12 [0,12,14] t3 b4
  have b5 : a 30 ≠ 4 := exclude [0,14] (fun u v => edge r77 v u) (a 30) (a 28) 4 t4 c77 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,6,10,12,20,21] := remove (a 30) 4 [0,1,4,6,10,12,20,21] d30 b5
  have b6 : a 30 ≠ 6 := exclude [0,14] (fun u v => edge r77 v u) (a 30) (a 28) 6 t4 c77 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,10,12,20,21] := remove (a 30) 6 [0,1,6,10,12,20,21] t5 b6
  have b7 : a 30 ≠ 10 := exclude [0,14] (fun u v => edge r77 v u) (a 30) (a 28) 10 t4 c77 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,12,20,21] := remove (a 30) 10 [0,1,10,12,20,21] t6 b7
  have b8 : a 30 ≠ 12 := exclude [0,14] (fun u v => edge r77 v u) (a 30) (a 28) 12 t4 c77 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,20,21] := remove (a 30) 12 [0,1,12,20,21] t7 b8
  have b9 : a 30 ≠ 20 := exclude [0,14] (fun u v => edge r77 v u) (a 30) (a 28) 20 t4 c77 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,21] := remove (a 30) 20 [0,1,20,21] t8 b9
  have b10 : a 30 ≠ 21 := exclude [0,14] (fun u v => edge r77 v u) (a 30) (a 28) 21 t4 c77 (by decide +kernel)
  have t10 : a 30 ∈ [0,1] := remove (a 30) 21 [0,1,21] t9 b10
  have b11 : a 4 ≠ 2 := exclude [0,12] (edge r18) (a 4) (a 12) 2 d12 c18 (by decide +kernel)
  have t11 : a 4 ∈ [0,6,8] := remove (a 4) 2 [0,2,6,8] d4 b11
  have b12 : a 4 ≠ 8 := exclude [0,12] (edge r18) (a 4) (a 12) 8 d12 c18 (by decide +kernel)
  have t12 : a 4 ∈ [0,6] := remove (a 4) 8 [0,6,8] t11 b12
  have b13 : a 6 ≠ 1 := exclude [0,2,7,9] (edge r25) (a 6) (a 22) 1 d22 c25 (by decide +kernel)
  have t13 : a 6 ∈ [0,4,5] := remove (a 6) 1 [0,1,4,5] d6 b13
  have b14 : a 6 ≠ 5 := exclude [0,2,7,9] (edge r25) (a 6) (a 22) 5 d22 c25 (by decide +kernel)
  have t14 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t13 b14
  have b15 : a 14 ≠ 1 := exclude [0,1] (edge r46) (a 14) (a 30) 1 t10 c46 (by decide +kernel)
  have t15 : a 14 ∈ [0,12,13] := remove (a 14) 1 [0,1,12,13] d14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))

theorem chunk15 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,12,13])
    (d30 : a 30 ∈ [0,1])
    (d18 : a 18 ∈ [0,6,10,12])
    (d19 : a 19 ∈ [0,6])
    (d22 : a 22 ∈ [0,2,7,9])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 14 ∈ [0,13] ∧ a 18 ∈ [0,12] ∧ a 22 ∈ [0,9] := by
  have b0 : a 14 ≠ 12 := exclude [0,1] (edge r46) (a 14) (a 30) 12 d30 c46 (by decide +kernel)
  have t0 : a 14 ∈ [0,13] := remove (a 14) 12 [0,12,13] d14 b0
  have b1 : a 18 ≠ 6 := exclude [0,6] (edge r55) (a 18) (a 19) 6 d19 c55 (by decide +kernel)
  have t1 : a 18 ∈ [0,10,12] := remove (a 18) 6 [0,6,10,12] d18 b1
  have b2 : a 18 ≠ 10 := exclude [0,6] (edge r55) (a 18) (a 19) 10 d19 c55 (by decide +kernel)
  have t2 : a 18 ∈ [0,12] := remove (a 18) 10 [0,10,12] t1 b2
  have b3 : a 22 ≠ 2 := exclude [0,1] (edge r66) (a 22) (a 30) 2 d30 c66 (by decide +kernel)
  have t3 : a 22 ∈ [0,7,9] := remove (a 22) 2 [0,2,7,9] d22 b3
  have b4 : a 22 ≠ 7 := exclude [0,1] (edge r66) (a 22) (a 30) 7 d30 c66 (by decide +kernel)
  have t4 : a 22 ∈ [0,9] := remove (a 22) 7 [0,7,9] t3 b4
  exact And.intro t0 (And.intro t2 (t4))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_210
