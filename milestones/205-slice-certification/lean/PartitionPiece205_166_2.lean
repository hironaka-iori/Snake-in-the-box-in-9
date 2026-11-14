import PartitionData205_166
namespace PartitionCover205_166
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,6,7,10,11,12,13,14,15,16,17])
    (d22 : a 22 ∈ [0,3])
    (d28 : a 28 ∈ [0,1,2,4,6,7,8,10])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d23 : a 23 ∈ [0,1,6,7])
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 20 ∈ [0,1,6,7] ∧ a 28 ∈ [0,1,6,7] ∧ a 21 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 20 ≠ 10 := exclude [0,3] (edge r61) (a 20) (a 22) 10 d22 c61 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 20) 10 [0,1,6,7,10,11,12,13,14,15,16,17] d20 b0
  have b1 : a 20 ≠ 11 := exclude [0,3] (edge r61) (a 20) (a 22) 11 d22 c61 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 20) 11 [0,1,6,7,11,12,13,14,15,16,17] t0 b1
  have b2 : a 20 ≠ 12 := exclude [0,3] (edge r61) (a 20) (a 22) 12 d22 c61 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,6,7,13,14,15,16,17] := remove (a 20) 12 [0,1,6,7,12,13,14,15,16,17] t1 b2
  have b3 : a 20 ≠ 13 := exclude [0,3] (edge r61) (a 20) (a 22) 13 d22 c61 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,6,7,14,15,16,17] := remove (a 20) 13 [0,1,6,7,13,14,15,16,17] t2 b3
  have b4 : a 20 ≠ 14 := exclude [0,3] (edge r61) (a 20) (a 22) 14 d22 c61 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,6,7,15,16,17] := remove (a 20) 14 [0,1,6,7,14,15,16,17] t3 b4
  have b5 : a 20 ≠ 15 := exclude [0,3] (edge r61) (a 20) (a 22) 15 d22 c61 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,6,7,16,17] := remove (a 20) 15 [0,1,6,7,15,16,17] t4 b5
  have b6 : a 20 ≠ 16 := exclude [0,3] (edge r61) (a 20) (a 22) 16 d22 c61 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,6,7,17] := remove (a 20) 16 [0,1,6,7,16,17] t5 b6
  have b7 : a 20 ≠ 17 := exclude [0,3] (edge r61) (a 20) (a 22) 17 d22 c61 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,6,7] := remove (a 20) 17 [0,1,6,7,17] t6 b7
  have b8 : a 28 ≠ 2 := exclude [0,1,6,7] (fun u v => edge r62 v u) (a 28) (a 20) 2 t7 c62 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,4,6,7,8,10] := remove (a 28) 2 [0,1,2,4,6,7,8,10] d28 b8
  have b9 : a 28 ≠ 4 := exclude [0,1,6,7] (fun u v => edge r62 v u) (a 28) (a 20) 4 t7 c62 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,6,7,8,10] := remove (a 28) 4 [0,1,4,6,7,8,10] t8 b9
  have b10 : a 28 ≠ 8 := exclude [0,1,6,7] (fun u v => edge r62 v u) (a 28) (a 20) 8 t7 c62 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,6,7,10] := remove (a 28) 8 [0,1,6,7,8,10] t9 b10
  have b11 : a 28 ≠ 10 := exclude [0,1,6,7] (fun u v => edge r62 v u) (a 28) (a 20) 10 t7 c62 (by decide +kernel)
  have t11 : a 28 ∈ [0,1,6,7] := remove (a 28) 10 [0,1,6,7,10] t10 b11
  have b12 : a 21 ≠ 2 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 2 d23 c63 (by decide +kernel)
  have t12 : a 21 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d21 b12
  have b13 : a 21 ≠ 3 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 3 d23 c63 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 21 ≠ 4 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 4 d23 c63 (by decide +kernel)
  have t14 : a 21 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 21 ≠ 5 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 5 d23 c63 (by decide +kernel)
  have t15 : a 21 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t7 (And.intro t11 (t15))

theorem chunk9 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17])
    (d23 : a 23 ∈ [0,1,6,7])
    (d29 : a 29 ∈ [0,1,2,6,7,9,10])
    (d30 : a 30 ∈ [0,1,3,4])
    (d22 : a 22 ∈ [0,3])
    (d31 : a 31 ∈ [0,1,2,3,12,13,14,15,20,22])
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 21 ∈ [0,1,6,7] ∧ a 29 ∈ [0,1,6,9] ∧ a 30 ∈ [0,3] ∧ a 31 ∈ [0,1,2,3,12,13,14,15,22] := by
  have b0 : a 21 ≠ 8 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 8 d23 c63 (by decide +kernel)
  have t0 : a 21 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 21) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] d21 b0
  have b1 : a 21 ≠ 9 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 9 d23 c63 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 21) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 21 ≠ 10 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 10 d23 c63 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 21) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 21 ≠ 11 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 11 d23 c63 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 21) 11 [0,1,6,7,11,12,13,14,15,16,17] t2 b3
  have b4 : a 21 ≠ 12 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 12 d23 c63 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,6,7,13,14,15,16,17] := remove (a 21) 12 [0,1,6,7,12,13,14,15,16,17] t3 b4
  have b5 : a 21 ≠ 13 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 13 d23 c63 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,6,7,14,15,16,17] := remove (a 21) 13 [0,1,6,7,13,14,15,16,17] t4 b5
  have b6 : a 21 ≠ 14 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 14 d23 c63 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,6,7,15,16,17] := remove (a 21) 14 [0,1,6,7,14,15,16,17] t5 b6
  have b7 : a 21 ≠ 15 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 15 d23 c63 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,6,7,16,17] := remove (a 21) 15 [0,1,6,7,15,16,17] t6 b7
  have b8 : a 21 ≠ 16 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 16 d23 c63 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,6,7,17] := remove (a 21) 16 [0,1,6,7,16,17] t7 b8
  have b9 : a 21 ≠ 17 := exclude [0,1,6,7] (edge r63) (a 21) (a 23) 17 d23 c63 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,6,7] := remove (a 21) 17 [0,1,6,7,17] t8 b9
  have b10 : a 29 ≠ 2 := exclude [0,1,6,7] (fun u v => edge r64 v u) (a 29) (a 21) 2 t9 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,6,7,9,10] := remove (a 29) 2 [0,1,2,6,7,9,10] d29 b10
  have b11 : a 29 ≠ 7 := exclude [0,1,6,7] (fun u v => edge r64 v u) (a 29) (a 21) 7 t9 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,6,9,10] := remove (a 29) 7 [0,1,6,7,9,10] t10 b11
  have b12 : a 29 ≠ 10 := exclude [0,1,6,7] (fun u v => edge r64 v u) (a 29) (a 21) 10 t9 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,6,9] := remove (a 29) 10 [0,1,6,9,10] t11 b12
  have b13 : a 30 ≠ 1 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t13 : a 30 ∈ [0,3,4] := remove (a 30) 1 [0,1,3,4] d30 b13
  have b14 : a 30 ≠ 4 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 4 d22 c66 (by decide +kernel)
  have t14 : a 30 ∈ [0,3] := remove (a 30) 4 [0,3,4] t13 b14
  have b15 : a 31 ≠ 20 := exclude [0,1,6,7] (fun u v => edge r67 v u) (a 31) (a 23) 20 d23 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,3,12,13,14,15,22] := remove (a 31) 20 [0,1,2,3,12,13,14,15,20,22] d31 b15
  exact And.intro t9 (And.intro t12 (And.intro t14 (t15)))

theorem chunk10 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,12,13,14,15,22])
    (d23 : a 23 ∈ [0,1,6,7])
    (d24 : a 24 ∈ [0,2,3,5])
    (d26 : a 26 ∈ [0])
    (d28 : a 28 ∈ [0,1,6,7])
    (d25 : a 25 ∈ [0,1,2,3,6,7,8,9])
    (d27 : a 27 ∈ [0])
    (d29 : a 29 ∈ [0,1,6,9])
    (c67 : edge r67 (a 23) (a 31)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 31 ∈ [0,2,13,14,15] ∧ a 24 ∈ [0,3] ∧ a 28 ∈ [0,6] ∧ a 25 ∈ [0,1] ∧ a 29 ∈ [0,1] := by
  have b0 : a 31 ≠ 22 := exclude [0,1,6,7] (fun u v => edge r67 v u) (a 31) (a 23) 22 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3,12,13,14,15] := remove (a 31) 22 [0,1,2,3,12,13,14,15,22] d31 b0
  have b1 : a 24 ≠ 2 := exclude [0] (edge r69) (a 24) (a 26) 2 d26 c69 (by decide +kernel)
  have t1 : a 24 ∈ [0,3,5] := remove (a 24) 2 [0,2,3,5] d24 b1
  have b2 : a 24 ≠ 5 := exclude [0] (edge r69) (a 24) (a 26) 5 d26 c69 (by decide +kernel)
  have t2 : a 24 ∈ [0,3] := remove (a 24) 5 [0,3,5] t1 b2
  have b3 : a 28 ≠ 1 := exclude [0,3] (fun u v => edge r70 v u) (a 28) (a 24) 1 t2 c70 (by decide +kernel)
  have t3 : a 28 ∈ [0,6,7] := remove (a 28) 1 [0,1,6,7] d28 b3
  have b4 : a 28 ≠ 7 := exclude [0,3] (fun u v => edge r70 v u) (a 28) (a 24) 7 t2 c70 (by decide +kernel)
  have t4 : a 28 ∈ [0,6] := remove (a 28) 7 [0,6,7] t3 b4
  have b5 : a 25 ≠ 6 := exclude [0] (edge r71) (a 25) (a 27) 6 d27 c71 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,2,3,7,8,9] := remove (a 25) 6 [0,1,2,3,6,7,8,9] d25 b5
  have b6 : a 25 ≠ 7 := exclude [0] (edge r71) (a 25) (a 27) 7 d27 c71 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,2,3,8,9] := remove (a 25) 7 [0,1,2,3,7,8,9] t5 b6
  have b7 : a 25 ≠ 8 := exclude [0] (edge r71) (a 25) (a 27) 8 d27 c71 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,2,3,9] := remove (a 25) 8 [0,1,2,3,8,9] t6 b7
  have b8 : a 25 ≠ 9 := exclude [0] (edge r71) (a 25) (a 27) 9 d27 c71 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,2,3] := remove (a 25) 9 [0,1,2,3,9] t7 b8
  have b9 : a 25 ≠ 2 := exclude [0,1,6,9] (edge r72) (a 25) (a 29) 2 d29 c72 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,3] := remove (a 25) 2 [0,1,2,3] t8 b9
  have b10 : a 25 ≠ 3 := exclude [0,1,6,9] (edge r72) (a 25) (a 29) 3 d29 c72 (by decide +kernel)
  have t10 : a 25 ∈ [0,1] := remove (a 25) 3 [0,1,3] t9 b10
  have b11 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r72 v u) (a 29) (a 25) 6 t10 c72 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,9] := remove (a 29) 6 [0,1,6,9] d29 b11
  have b12 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r72 v u) (a 29) (a 25) 9 t10 c72 (by decide +kernel)
  have t12 : a 29 ∈ [0,1] := remove (a 29) 9 [0,1,9] t11 b12
  have b13 : a 31 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 1 d27 c75 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,3,12,13,14,15] := remove (a 31) 1 [0,1,2,3,12,13,14,15] t0 b13
  have b14 : a 31 ≠ 3 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 3 d27 c75 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,12,13,14,15] := remove (a 31) 3 [0,2,3,12,13,14,15] t13 b14
  have b15 : a 31 ≠ 12 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 12 d27 c75 (by decide +kernel)
  have t15 : a 31 ∈ [0,2,13,14,15] := remove (a 31) 12 [0,2,12,13,14,15] t14 b15
  exact And.intro t15 (And.intro t2 (And.intro t4 (And.intro t10 (t12))))

theorem chunk11 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,2,13,14,15])
    (d27 : a 27 ∈ [0])
    (d30 : a 30 ∈ [0,3])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,2])
    (d13 : a 13 ∈ [0,2,4,6])
    (d14 : a 14 ∈ [0,2])
    (d17 : a 17 ∈ [0,1,2,3,6,7,8,9])
    (d16 : a 16 ∈ [0,6])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 31 ∈ [0,2] ∧ a 30 ∈ [0] ∧ a 5 ∈ [0,2] ∧ a 13 ∈ [0,4] ∧ a 14 ∈ [0] ∧ a 17 ∈ [0,6,9] := by
  have b0 : a 31 ≠ 13 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 13 d27 c75 (by decide +kernel)
  have t0 : a 31 ∈ [0,2,14,15] := remove (a 31) 13 [0,2,13,14,15] d31 b0
  have b1 : a 31 ≠ 14 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 14 d27 c75 (by decide +kernel)
  have t1 : a 31 ∈ [0,2,15] := remove (a 31) 14 [0,2,14,15] t0 b1
  have b2 : a 31 ≠ 15 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 15 d27 c75 (by decide +kernel)
  have t2 : a 31 ∈ [0,2] := remove (a 31) 15 [0,2,15] t1 b2
  have b3 : a 30 ≠ 3 := exclude [0,2] (edge r79) (a 30) (a 31) 3 t2 c79 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 3 [0,3] d30 b3
  have b4 : a 5 ≠ 1 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t4 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b4
  have b5 : a 5 ≠ 3 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t5 : a 5 ∈ [0,2,4,5] := remove (a 5) 3 [0,2,3,4,5] t4 b5
  have b6 : a 5 ≠ 4 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,5] := remove (a 5) 4 [0,2,4,5] t5 b6
  have b7 : a 5 ≠ 5 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 5 d4 c16 (by decide +kernel)
  have t7 : a 5 ∈ [0,2] := remove (a 5) 5 [0,2,5] t6 b7
  have b8 : a 13 ≠ 2 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 2 t7 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,4,6] := remove (a 13) 2 [0,2,4,6] d13 b8
  have b9 : a 13 ≠ 6 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 6 t7 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,4] := remove (a 13) 6 [0,4,6] t8 b9
  have b10 : a 14 ≠ 2 := exclude [0] (edge r46) (a 14) (a 30) 2 t3 c46 (by decide +kernel)
  have t10 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b10
  have b11 : a 17 ≠ 1 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 1 d16 c48 (by decide +kernel)
  have t11 : a 17 ∈ [0,2,3,6,7,8,9] := remove (a 17) 1 [0,1,2,3,6,7,8,9] d17 b11
  have b12 : a 17 ≠ 2 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,3,6,7,8,9] := remove (a 17) 2 [0,2,3,6,7,8,9] t11 b12
  have b13 : a 17 ≠ 3 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 3 d16 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0,6,7,8,9] := remove (a 17) 3 [0,3,6,7,8,9] t12 b13
  have b14 : a 17 ≠ 7 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 7 d16 c48 (by decide +kernel)
  have t14 : a 17 ∈ [0,6,8,9] := remove (a 17) 7 [0,6,7,8,9] t13 b14
  have b15 : a 17 ≠ 8 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 8 d16 c48 (by decide +kernel)
  have t15 : a 17 ∈ [0,6,9] := remove (a 17) 8 [0,6,8,9] t14 b15
  exact And.intro t2 (And.intro t3 (And.intro t7 (And.intro t9 (And.intro t10 (t15)))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_166
