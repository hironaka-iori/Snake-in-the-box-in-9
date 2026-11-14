import PartitionData205_212
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,2,3,4,5])
    (d17 : a 17 ∈ [0,6])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d18 : a 18 ∈ [0,1,6,7])
    (d19 : a 19 ∈ [0,1,6,7])
    (d23 : a 23 ∈ [0,2,3,4,6,7,8])
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    : a 21 ∈ [0,2,3,5] ∧ a 25 ∈ [0,1] ∧ a 22 ∈ [0,1] ∧ a 19 ∈ [0,6] ∧ a 23 ∈ [0,3,4,6,7,8] := by
  have b0 : a 21 ≠ 4 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t0 : a 21 ∈ [0,2,3,5] := remove (a 21) 4 [0,2,3,4,5] d21 b0
  have b1 : a 25 ≠ 2 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 2 d17 c54 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,3,4,5] := remove (a 25) 2 [0,1,2,3,4,5] d25 b1
  have b2 : a 25 ≠ 3 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 3 d17 c54 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,4,5] := remove (a 25) 3 [0,1,3,4,5] t1 b2
  have b3 : a 25 ≠ 4 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 4 d17 c54 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,5] := remove (a 25) 4 [0,1,4,5] t2 b3
  have b4 : a 25 ≠ 5 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 5 d17 c54 (by decide +kernel)
  have t4 : a 25 ∈ [0,1] := remove (a 25) 5 [0,1,5] t3 b4
  have b5 : a 22 ≠ 2 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 2 d18 c56 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 22) 2 [0,1,2,3,4,5,6,7,8,9] d22 b5
  have b6 : a 22 ≠ 3 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t6 : a 22 ∈ [0,1,4,5,6,7,8,9] := remove (a 22) 3 [0,1,3,4,5,6,7,8,9] t5 b6
  have b7 : a 22 ≠ 4 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t7 : a 22 ∈ [0,1,5,6,7,8,9] := remove (a 22) 4 [0,1,4,5,6,7,8,9] t6 b7
  have b8 : a 22 ≠ 5 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,6,7,8,9] := remove (a 22) 5 [0,1,5,6,7,8,9] t7 b8
  have b9 : a 22 ≠ 6 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 6 d18 c56 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,7,8,9] := remove (a 22) 6 [0,1,6,7,8,9] t8 b9
  have b10 : a 22 ≠ 7 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 7 d18 c56 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,8,9] := remove (a 22) 7 [0,1,7,8,9] t9 b10
  have b11 : a 22 ≠ 8 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 8 d18 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,9] := remove (a 22) 8 [0,1,8,9] t10 b11
  have b12 : a 22 ≠ 9 := exclude [0,1,6,7] (fun u v => edge r56 v u) (a 22) (a 18) 9 d18 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,1] := remove (a 22) 9 [0,1,9] t11 b12
  have b13 : a 19 ≠ 1 := exclude [0,2,3,4,6,7,8] (edge r58) (a 19) (a 23) 1 d23 c58 (by decide +kernel)
  have t13 : a 19 ∈ [0,6,7] := remove (a 19) 1 [0,1,6,7] d19 b13
  have b14 : a 19 ≠ 7 := exclude [0,2,3,4,6,7,8] (edge r58) (a 19) (a 23) 7 d23 c58 (by decide +kernel)
  have t14 : a 19 ∈ [0,6] := remove (a 19) 7 [0,6,7] t13 b14
  have b15 : a 23 ≠ 2 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 2 t14 c58 (by decide +kernel)
  have t15 : a 23 ∈ [0,3,4,6,7,8] := remove (a 23) 2 [0,2,3,4,6,7,8] d23 b15
  exact And.intro t0 (And.intro t4 (And.intro t12 (And.intro t14 (t15))))

theorem chunk21 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,3,4,6,7,8])
    (d19 : a 19 ∈ [0,6])
    (d21 : a 21 ∈ [0,2,3,5])
    (d20 : a 20 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 23 ∈ [0] ∧ a 21 ∈ [0] ∧ a 29 ∈ [0] ∧ a 22 ∈ [0] ∧ a 31 ∈ [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 23 ≠ 3 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,4,6,7,8] := remove (a 23) 3 [0,3,4,6,7,8] d23 b0
  have b1 : a 23 ≠ 4 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,6,7,8] := remove (a 23) 4 [0,4,6,7,8] t0 b1
  have b2 : a 23 ≠ 6 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 6 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,7,8] := remove (a 23) 6 [0,6,7,8] t1 b2
  have b3 : a 23 ≠ 7 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,8] := remove (a 23) 7 [0,7,8] t2 b3
  have b4 : a 23 ≠ 8 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 8 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0] := remove (a 23) 8 [0,8] t3 b4
  have b5 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r60 v u) (a 21) (a 20) 3 d20 c60 (by decide +kernel)
  have t5 : a 21 ∈ [0,2,5] := remove (a 21) 3 [0,2,3,5] d21 b5
  have b6 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r60 v u) (a 21) (a 20) 5 d20 c60 (by decide +kernel)
  have t6 : a 21 ∈ [0,2] := remove (a 21) 5 [0,2,5] t5 b6
  have b7 : a 21 ≠ 2 := exclude [0] (edge r63) (a 21) (a 23) 2 t4 c63 (by decide +kernel)
  have t7 : a 21 ∈ [0] := remove (a 21) 2 [0,2] t6 b7
  have b8 : a 29 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 1 t7 c64 (by decide +kernel)
  have t8 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b8
  have b9 : a 22 ≠ 1 := exclude [0] (edge r65) (a 22) (a 23) 1 t4 c65 (by decide +kernel)
  have t9 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b9
  have b10 : a 31 ≠ 2 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 2 t4 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b10
  have b11 : a 31 ≠ 3 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 3 t4 c67 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 31 ≠ 4 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 4 t4 c67 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 31 ≠ 5 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 5 t4 c67 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 31 ≠ 8 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 8 t4 c67 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 31 ≠ 9 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 9 t4 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t4 (And.intro t7 (And.intro t8 (And.intro t9 (t15))))

theorem chunk22 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d23 : a 23 ∈ [0])
    (d26 : a 26 ∈ [0,2,3,5])
    (d24 : a 24 ∈ [0,12])
    (d28 : a 28 ∈ [0,2])
    (c67 : edge r67 (a 23) (a 31)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    : a 31 ∈ [0,1,6,7,20,21] ∧ a 26 ∈ [0,2] ∧ a 24 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 31 ≠ 10 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 10 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 10 [0,1,6,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d31 b0
  have b1 : a 31 ≠ 11 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 11 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 11 [0,1,6,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 31 ≠ 12 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 12 d23 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 12 [0,1,6,7,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 31 ≠ 13 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 13 d23 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,6,7,14,15,16,17,18,19,20,21,22,23] := remove (a 31) 13 [0,1,6,7,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 31 ≠ 14 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 14 d23 c67 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,6,7,15,16,17,18,19,20,21,22,23] := remove (a 31) 14 [0,1,6,7,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 31 ≠ 15 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 15 d23 c67 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,6,7,16,17,18,19,20,21,22,23] := remove (a 31) 15 [0,1,6,7,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 31 ≠ 16 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 16 d23 c67 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,6,7,17,18,19,20,21,22,23] := remove (a 31) 16 [0,1,6,7,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 31 ≠ 17 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 17 d23 c67 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,6,7,18,19,20,21,22,23] := remove (a 31) 17 [0,1,6,7,17,18,19,20,21,22,23] t6 b7
  have b8 : a 31 ≠ 18 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 18 d23 c67 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,6,7,19,20,21,22,23] := remove (a 31) 18 [0,1,6,7,18,19,20,21,22,23] t7 b8
  have b9 : a 31 ≠ 19 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 19 d23 c67 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,6,7,20,21,22,23] := remove (a 31) 19 [0,1,6,7,19,20,21,22,23] t8 b9
  have b10 : a 31 ≠ 22 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 22 d23 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,6,7,20,21,23] := remove (a 31) 22 [0,1,6,7,20,21,22,23] t9 b10
  have b11 : a 31 ≠ 23 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 23 d23 c67 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,6,7,20,21] := remove (a 31) 23 [0,1,6,7,20,21,23] t10 b11
  have b12 : a 26 ≠ 3 := exclude [0,12] (fun u v => edge r69 v u) (a 26) (a 24) 3 d24 c69 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,5] := remove (a 26) 3 [0,2,3,5] d26 b12
  have b13 : a 26 ≠ 5 := exclude [0,12] (fun u v => edge r69 v u) (a 26) (a 24) 5 d24 c69 (by decide +kernel)
  have t13 : a 26 ∈ [0,2] := remove (a 26) 5 [0,2,5] t12 b13
  have b14 : a 24 ≠ 12 := exclude [0,2] (edge r70) (a 24) (a 28) 12 d28 c70 (by decide +kernel)
  have t14 : a 24 ∈ [0] := remove (a 24) 12 [0,12] d24 b14
  have b15 : a 28 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 2 t14 c70 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b15
  exact And.intro t11 (And.intro t13 (And.intro t14 (t15)))

theorem chunk23 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,12,13])
    (d25 : a 25 ∈ [0,1])
    (d29 : a 29 ∈ [0])
    (d31 : a 31 ∈ [0,1,6,7,20,21])
    (d30 : a 30 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d4 : a 4 ∈ [0,1,3])
    (d12 : a 12 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,4,5,10])
    (d14 : a 14 ∈ [0])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 27 ∈ [0,1] ∧ a 25 ∈ [0] ∧ a 31 ∈ [0] ∧ a 30 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 6 ∈ [0,1] := by
  have b0 : a 27 ≠ 12 := exclude [0,1] (fun u v => edge r71 v u) (a 27) (a 25) 12 d25 c71 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,13] := remove (a 27) 12 [0,1,12,13] d27 b0
  have b1 : a 27 ≠ 13 := exclude [0,1] (fun u v => edge r71 v u) (a 27) (a 25) 13 d25 c71 (by decide +kernel)
  have t1 : a 27 ∈ [0,1] := remove (a 27) 13 [0,1,13] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0] (edge r72) (a 25) (a 29) 1 d29 c72 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b2
  have b3 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r75 v u) (a 31) (a 27) 6 t1 c75 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,7,20,21] := remove (a 31) 6 [0,1,6,7,20,21] d31 b3
  have b4 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r75 v u) (a 31) (a 27) 7 t1 c75 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,20,21] := remove (a 31) 7 [0,1,7,20,21] t3 b4
  have b5 : a 31 ≠ 20 := exclude [0,1] (fun u v => edge r75 v u) (a 31) (a 27) 20 t1 c75 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,21] := remove (a 31) 20 [0,1,20,21] t4 b5
  have b6 : a 31 ≠ 21 := exclude [0,1] (fun u v => edge r75 v u) (a 31) (a 27) 21 t1 c75 (by decide +kernel)
  have t6 : a 31 ∈ [0,1] := remove (a 31) 21 [0,1,21] t5 b6
  have b7 : a 30 ≠ 1 := exclude [0] (fun u v => edge r77 v u) (a 30) (a 28) 1 d28 c77 (by decide +kernel)
  have t7 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b7
  have b8 : a 31 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 31) (a 29) 1 d29 c78 (by decide +kernel)
  have t8 : a 31 ∈ [0] := remove (a 31) 1 [0,1] t6 b8
  have b9 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t9 : a 4 ∈ [0,3] := remove (a 4) 1 [0,1,3] d4 b9
  have b10 : a 4 ≠ 3 := exclude [0] (edge r18) (a 4) (a 12) 3 d12 c18 (by decide +kernel)
  have t10 : a 4 ∈ [0] := remove (a 4) 3 [0,3] t9 b10
  have b11 : a 5 ≠ 1 := exclude [0] (edge r22) (a 5) (a 21) 1 d21 c22 (by decide +kernel)
  have t11 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b11
  have b12 : a 6 ≠ 2 := exclude [0] (edge r24) (a 6) (a 14) 2 d14 c24 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,4,5,10] := remove (a 6) 2 [0,1,2,4,5,10] d6 b12
  have b13 : a 6 ≠ 4 := exclude [0] (edge r24) (a 6) (a 14) 4 d14 c24 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,5,10] := remove (a 6) 4 [0,1,4,5,10] t12 b13
  have b14 : a 6 ≠ 5 := exclude [0] (edge r24) (a 6) (a 14) 5 d14 c24 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,10] := remove (a 6) 5 [0,1,5,10] t13 b14
  have b15 : a 6 ≠ 10 := exclude [0] (edge r24) (a 6) (a 14) 10 d14 c24 (by decide +kernel)
  have t15 : a 6 ∈ [0,1] := remove (a 6) 10 [0,1,10] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t8 (And.intro t7 (And.intro t10 (And.intro t11 (t15))))))

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_212
