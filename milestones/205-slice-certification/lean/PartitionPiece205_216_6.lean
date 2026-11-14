import PartitionData205_216
namespace PartitionCover205_216
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,5,14,18,19])
    (d16 : a 16 ∈ [0,8,12,22])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d17 : a 17 ∈ [0,4])
    (d21 : a 21 ∈ [0,1,2,4])
    (d25 : a 25 ∈ [0,1,7])
    (d18 : a 18 ∈ [0,2,3,6,8,11])
    (d22 : a 22 ∈ [0,2,12,14])
    (d23 : a 23 ∈ [0,1,3])
    (d27 : a 27 ∈ [0,1])
    (c51 : edge r51 (a 16) (a 24)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 24 ∈ [0,1,18,19] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0,2] ∧ a 25 ∈ [0,1] ∧ a 18 ∈ [0,2,6,8] ∧ a 22 ∈ [0,2,14] ∧ a 23 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 24 ≠ 5 := exclude [0,8,12,22] (fun u v => edge r51 v u) (a 24) (a 16) 5 d16 c51 (by decide +kernel)
  have t0 : a 24 ∈ [0,1,14,18,19] := remove (a 24) 5 [0,1,5,14,18,19] d24 b0
  have b1 : a 24 ≠ 14 := exclude [0,8,12,22] (fun u v => edge r51 v u) (a 24) (a 16) 14 d16 c51 (by decide +kernel)
  have t1 : a 24 ∈ [0,1,18,19] := remove (a 24) 14 [0,1,14,18,19] t0 b1
  have b2 : a 19 ≠ 1 := exclude [0,4] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b2
  have b3 : a 19 ≠ 3 := exclude [0,4] (fun u v => edge r52 v u) (a 19) (a 17) 3 d17 c52 (by decide +kernel)
  have t3 : a 19 ∈ [0,2,4,5] := remove (a 19) 3 [0,2,3,4,5] t2 b3
  have b4 : a 19 ≠ 4 := exclude [0,4] (fun u v => edge r52 v u) (a 19) (a 17) 4 d17 c52 (by decide +kernel)
  have t4 : a 19 ∈ [0,2,5] := remove (a 19) 4 [0,2,4,5] t3 b4
  have b5 : a 19 ≠ 5 := exclude [0,4] (fun u v => edge r52 v u) (a 19) (a 17) 5 d17 c52 (by decide +kernel)
  have t5 : a 19 ∈ [0,2] := remove (a 19) 5 [0,2,5] t4 b5
  have b6 : a 21 ≠ 1 := exclude [0,4] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t6 : a 21 ∈ [0,2,4] := remove (a 21) 1 [0,1,2,4] d21 b6
  have b7 : a 21 ≠ 4 := exclude [0,4] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0,2] := remove (a 21) 4 [0,2,4] t6 b7
  have b8 : a 25 ≠ 7 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 7 d17 c54 (by decide +kernel)
  have t8 : a 25 ∈ [0,1] := remove (a 25) 7 [0,1,7] d25 b8
  have b9 : a 18 ≠ 3 := exclude [0,2] (edge r55) (a 18) (a 19) 3 t5 c55 (by decide +kernel)
  have t9 : a 18 ∈ [0,2,6,8,11] := remove (a 18) 3 [0,2,3,6,8,11] d18 b9
  have b10 : a 18 ≠ 11 := exclude [0,2] (edge r55) (a 18) (a 19) 11 t5 c55 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,6,8] := remove (a 18) 11 [0,2,6,8,11] t9 b10
  have b11 : a 22 ≠ 12 := exclude [0,2,6,8] (fun u v => edge r56 v u) (a 22) (a 18) 12 t10 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,14] := remove (a 22) 12 [0,2,12,14] d22 b11
  have b12 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 1 t5 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,3] := remove (a 23) 1 [0,1,3] d23 b12
  have b13 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 3 t5 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0] := remove (a 23) 3 [0,3] t12 b13
  have b14 : a 19 ≠ 2 := exclude [0,1] (edge r59) (a 19) (a 27) 2 d27 c59 (by decide +kernel)
  have t14 : a 19 ∈ [0] := remove (a 19) 2 [0,2] t5 b14
  have b15 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 t14 c59 (by decide +kernel)
  have t15 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b15
  exact And.intro t1 (And.intro t14 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t13 (t15)))))))

theorem chunk25 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,13,18,19,21])
    (d21 : a 21 ∈ [0,2])
    (d22 : a 22 ∈ [0,2,14])
    (d29 : a 29 ∈ [0,11,21])
    (d23 : a 23 ∈ [0])
    (d24 : a 24 ∈ [0,1,18,19])
    (d26 : a 26 ∈ [0,1])
    (d28 : a 28 ∈ [0,2])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d31 : a 31 ∈ [0,2,5,11])
    (d27 : a 27 ∈ [0])
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 20 ∈ [0] ∧ a 22 ∈ [0] ∧ a 29 ∈ [0,21] ∧ a 24 ∈ [0] ∧ a 30 ∈ [0,1,3,5] ∧ a 31 ∈ [0] := by
  have b0 : a 20 ≠ 1 := exclude [0,2] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t0 : a 20 ∈ [0,13,18,19,21] := remove (a 20) 1 [0,1,13,18,19,21] d20 b0
  have b1 : a 20 ≠ 13 := exclude [0,2] (edge r60) (a 20) (a 21) 13 d21 c60 (by decide +kernel)
  have t1 : a 20 ∈ [0,18,19,21] := remove (a 20) 13 [0,13,18,19,21] t0 b1
  have b2 : a 20 ≠ 19 := exclude [0,2] (edge r60) (a 20) (a 21) 19 d21 c60 (by decide +kernel)
  have t2 : a 20 ∈ [0,18,21] := remove (a 20) 19 [0,18,19,21] t1 b2
  have b3 : a 20 ≠ 21 := exclude [0,2] (edge r60) (a 20) (a 21) 21 d21 c60 (by decide +kernel)
  have t3 : a 20 ∈ [0,18] := remove (a 20) 21 [0,18,21] t2 b3
  have b4 : a 20 ≠ 18 := exclude [0,2,14] (edge r61) (a 20) (a 22) 18 d22 c61 (by decide +kernel)
  have t4 : a 20 ∈ [0] := remove (a 20) 18 [0,18] t3 b4
  have b5 : a 22 ≠ 14 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 14 t4 c61 (by decide +kernel)
  have t5 : a 22 ∈ [0,2] := remove (a 22) 14 [0,2,14] d22 b5
  have b6 : a 29 ≠ 11 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 11 d21 c64 (by decide +kernel)
  have t6 : a 29 ∈ [0,21] := remove (a 29) 11 [0,11,21] d29 b6
  have b7 : a 22 ≠ 2 := exclude [0] (edge r65) (a 22) (a 23) 2 d23 c65 (by decide +kernel)
  have t7 : a 22 ∈ [0] := remove (a 22) 2 [0,2] t5 b7
  have b8 : a 24 ≠ 18 := exclude [0,1] (edge r69) (a 24) (a 26) 18 d26 c69 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,19] := remove (a 24) 18 [0,1,18,19] d24 b8
  have b9 : a 24 ≠ 19 := exclude [0,1] (edge r69) (a 24) (a 26) 19 d26 c69 (by decide +kernel)
  have t9 : a 24 ∈ [0,1] := remove (a 24) 19 [0,1,19] t8 b9
  have b10 : a 24 ≠ 1 := exclude [0,2] (edge r70) (a 24) (a 28) 1 d28 c70 (by decide +kernel)
  have t10 : a 24 ∈ [0] := remove (a 24) 1 [0,1] t9 b10
  have b11 : a 30 ≠ 2 := exclude [0,1] (fun u v => edge r74 v u) (a 30) (a 26) 2 d26 c74 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,3,4,5] := remove (a 30) 2 [0,1,2,3,4,5] d30 b11
  have b12 : a 30 ≠ 4 := exclude [0,1] (fun u v => edge r74 v u) (a 30) (a 26) 4 d26 c74 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,3,5] := remove (a 30) 4 [0,1,3,4,5] t11 b12
  have b13 : a 31 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 2 d27 c75 (by decide +kernel)
  have t13 : a 31 ∈ [0,5,11] := remove (a 31) 2 [0,2,5,11] d31 b13
  have b14 : a 31 ≠ 5 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 5 d27 c75 (by decide +kernel)
  have t14 : a 31 ∈ [0,11] := remove (a 31) 5 [0,5,11] t13 b14
  have b15 : a 31 ≠ 11 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 11 d27 c75 (by decide +kernel)
  have t15 : a 31 ∈ [0] := remove (a 31) 11 [0,11] t14 b15
  exact And.intro t4 (And.intro t7 (And.intro t6 (And.intro t10 (And.intro t12 (t15)))))

theorem chunk26 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,21])
    (d28 : a 28 ∈ [0,2])
    (d30 : a 30 ∈ [0,1,3,5])
    (d31 : a 31 ∈ [0])
    (d1 : a 1 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,4])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0])
    (d3 : a 3 ∈ [0,1,2])
    (d11 : a 11 ∈ [0])
    (d4 : a 4 ∈ [0,1,4,5,21,23])
    (d12 : a 12 ∈ [0])
    (d6 : a 6 ∈ [0,2,12,14])
    (d22 : a 22 ∈ [0])
    (d7 : a 7 ∈ [0,1,6,7,12,13,16,17])
    (d15 : a 15 ∈ [0,5])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 1 ∈ [0,1] ∧ a 2 ∈ [0] ∧ a 3 ∈ [0] ∧ a 4 ∈ [0,4] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0,6,7,12,13,16,17] := by
  have b0 : a 29 ≠ 21 := exclude [0,2] (fun u v => edge r76 v u) (a 29) (a 28) 21 d28 c76 (by decide +kernel)
  have t0 : a 29 ∈ [0] := remove (a 29) 21 [0,21] d29 b0
  have b1 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r77 v u) (a 30) (a 28) 3 d28 c77 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,5] := remove (a 30) 3 [0,1,3,5] d30 b1
  have b2 : a 30 ≠ 5 := exclude [0,2] (fun u v => edge r77 v u) (a 30) (a 28) 5 d28 c77 (by decide +kernel)
  have t2 : a 30 ∈ [0,1] := remove (a 30) 5 [0,1,5] t1 b2
  have b3 : a 30 ≠ 1 := exclude [0] (edge r79) (a 30) (a 31) 1 d31 c79 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 1 [0,1] t2 b3
  have b4 : a 1 ≠ 2 := exclude [0,4] (edge r8) (a 1) (a 17) 2 d17 c8 (by decide +kernel)
  have t4 : a 1 ∈ [0,1] := remove (a 1) 2 [0,1,2] d1 b4
  have b5 : a 2 ≠ 2 := exclude [0] (edge r11) (a 2) (a 10) 2 d10 c11 (by decide +kernel)
  have t5 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b5
  have b6 : a 3 ≠ 1 := exclude [0] (edge r14) (a 3) (a 11) 1 d11 c14 (by decide +kernel)
  have t6 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b6
  have b7 : a 3 ≠ 2 := exclude [0] (edge r14) (a 3) (a 11) 2 d11 c14 (by decide +kernel)
  have t7 : a 3 ∈ [0] := remove (a 3) 2 [0,2] t6 b7
  have b8 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t8 : a 4 ∈ [0,4,5,21,23] := remove (a 4) 1 [0,1,4,5,21,23] d4 b8
  have b9 : a 4 ≠ 5 := exclude [0] (edge r18) (a 4) (a 12) 5 d12 c18 (by decide +kernel)
  have t9 : a 4 ∈ [0,4,21,23] := remove (a 4) 5 [0,4,5,21,23] t8 b9
  have b10 : a 4 ≠ 21 := exclude [0] (edge r18) (a 4) (a 12) 21 d12 c18 (by decide +kernel)
  have t10 : a 4 ∈ [0,4,23] := remove (a 4) 21 [0,4,21,23] t9 b10
  have b11 : a 4 ≠ 23 := exclude [0] (edge r18) (a 4) (a 12) 23 d12 c18 (by decide +kernel)
  have t11 : a 4 ∈ [0,4] := remove (a 4) 23 [0,4,23] t10 b11
  have b12 : a 6 ≠ 2 := exclude [0] (edge r25) (a 6) (a 22) 2 d22 c25 (by decide +kernel)
  have t12 : a 6 ∈ [0,12,14] := remove (a 6) 2 [0,2,12,14] d6 b12
  have b13 : a 6 ≠ 12 := exclude [0] (edge r25) (a 6) (a 22) 12 d22 c25 (by decide +kernel)
  have t13 : a 6 ∈ [0,14] := remove (a 6) 12 [0,12,14] t12 b13
  have b14 : a 6 ≠ 14 := exclude [0] (edge r25) (a 6) (a 22) 14 d22 c25 (by decide +kernel)
  have t14 : a 6 ∈ [0] := remove (a 6) 14 [0,14] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0,5] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t15 : a 7 ∈ [0,6,7,12,13,16,17] := remove (a 7) 1 [0,1,6,7,12,13,16,17] d7 b15
  exact And.intro t0 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t11 (And.intro t14 (t15)))))))

theorem chunk27 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,6,7,12,13,16,17])
    (d15 : a 15 ∈ [0,5])
    (d8 : a 8 ∈ [0,1,7])
    (d10 : a 10 ∈ [0])
    (d12 : a 12 ∈ [0])
    (d9 : a 9 ∈ [0,6,12])
    (d11 : a 11 ∈ [0])
    (d13 : a 13 ∈ [0,2,3])
    (d25 : a 25 ∈ [0,1])
    (d16 : a 16 ∈ [0,8,12,22])
    (d24 : a 24 ∈ [0])
    (d17 : a 17 ∈ [0,4])
    (d19 : a 19 ∈ [0])
    (d18 : a 18 ∈ [0,2,6,8])
    (d22 : a 22 ∈ [0])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 7 ∈ [0,6,12] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 15 ∈ [0] ∧ a 16 ∈ [0,12] ∧ a 17 ∈ [0] ∧ a 18 ∈ [0,2,8] := by
  have b0 : a 7 ≠ 7 := exclude [0,5] (edge r26) (a 7) (a 15) 7 d15 c26 (by decide +kernel)
  have t0 : a 7 ∈ [0,6,12,13,16,17] := remove (a 7) 7 [0,6,7,12,13,16,17] d7 b0
  have b1 : a 7 ≠ 13 := exclude [0,5] (edge r26) (a 7) (a 15) 13 d15 c26 (by decide +kernel)
  have t1 : a 7 ∈ [0,6,12,16,17] := remove (a 7) 13 [0,6,12,13,16,17] t0 b1
  have b2 : a 7 ≠ 16 := exclude [0,5] (edge r26) (a 7) (a 15) 16 d15 c26 (by decide +kernel)
  have t2 : a 7 ∈ [0,6,12,17] := remove (a 7) 16 [0,6,12,16,17] t1 b2
  have b3 : a 7 ≠ 17 := exclude [0,5] (edge r26) (a 7) (a 15) 17 d15 c26 (by decide +kernel)
  have t3 : a 7 ∈ [0,6,12] := remove (a 7) 17 [0,6,12,17] t2 b3
  have b4 : a 8 ≠ 7 := exclude [0] (edge r29) (a 8) (a 10) 7 d10 c29 (by decide +kernel)
  have t4 : a 8 ∈ [0,1] := remove (a 8) 7 [0,1,7] d8 b4
  have b5 : a 8 ≠ 1 := exclude [0] (edge r30) (a 8) (a 12) 1 d12 c30 (by decide +kernel)
  have t5 : a 8 ∈ [0] := remove (a 8) 1 [0,1] t4 b5
  have b6 : a 9 ≠ 6 := exclude [0] (edge r32) (a 9) (a 11) 6 d11 c32 (by decide +kernel)
  have t6 : a 9 ∈ [0,12] := remove (a 9) 6 [0,6,12] d9 b6
  have b7 : a 9 ≠ 12 := exclude [0] (edge r32) (a 9) (a 11) 12 d11 c32 (by decide +kernel)
  have t7 : a 9 ∈ [0] := remove (a 9) 12 [0,12] t6 b7
  have b8 : a 13 ≠ 2 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 2 t7 c33 (by decide +kernel)
  have t8 : a 13 ∈ [0,3] := remove (a 13) 2 [0,2,3] d13 b8
  have b9 : a 13 ≠ 3 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 3 t7 c33 (by decide +kernel)
  have t9 : a 13 ∈ [0] := remove (a 13) 3 [0,3] t8 b9
  have b10 : a 25 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 1 t7 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b10
  have b11 : a 15 ≠ 5 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 5 t9 c43 (by decide +kernel)
  have t11 : a 15 ∈ [0] := remove (a 15) 5 [0,5] d15 b11
  have b12 : a 16 ≠ 8 := exclude [0] (edge r51) (a 16) (a 24) 8 d24 c51 (by decide +kernel)
  have t12 : a 16 ∈ [0,12,22] := remove (a 16) 8 [0,8,12,22] d16 b12
  have b13 : a 16 ≠ 22 := exclude [0] (edge r51) (a 16) (a 24) 22 d24 c51 (by decide +kernel)
  have t13 : a 16 ∈ [0,12] := remove (a 16) 22 [0,12,22] t12 b13
  have b14 : a 17 ≠ 4 := exclude [0] (edge r52) (a 17) (a 19) 4 d19 c52 (by decide +kernel)
  have t14 : a 17 ∈ [0] := remove (a 17) 4 [0,4] d17 b14
  have b15 : a 18 ≠ 6 := exclude [0] (edge r56) (a 18) (a 22) 6 d22 c56 (by decide +kernel)
  have t15 : a 18 ∈ [0,2,8] := remove (a 18) 6 [0,2,6,8] d18 b15
  exact And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))))))

#print axioms chunk24
#print axioms chunk25
#print axioms chunk26
#print axioms chunk27
end PartitionCover205_216
