import PartitionData205_196
namespace PartitionCover205_196
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,12,13,18,19,20,22])
    (d18 : a 18 ∈ [0,3])
    (d27 : a 27 ∈ [0,1,7])
    (d19 : a 19 ∈ [0,3])
    (d23 : a 23 ∈ [0,1,2,4])
    (d21 : a 21 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,6,7,8])
    (d22 : a 22 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c57 : edge r57 (a 18) (a 26)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 26 ∈ [0,1,12,13,20,22] ∧ a 27 ∈ [0] ∧ a 23 ∈ [0,1] ∧ a 30 ∈ [0,2,6,8] ∧ a 31 ∈ [0,1,8,9,14,15,16,17,18,19] := by
  have b0 : a 26 ≠ 18 := exclude [0,3] (fun u v => edge r57 v u) (a 26) (a 18) 18 d18 c57 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,12,13,19,20,22] := remove (a 26) 18 [0,1,12,13,18,19,20,22] d26 b0
  have b1 : a 26 ≠ 19 := exclude [0,3] (fun u v => edge r57 v u) (a 26) (a 18) 19 d18 c57 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,12,13,20,22] := remove (a 26) 19 [0,1,12,13,19,20,22] t0 b1
  have b2 : a 27 ≠ 1 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t2 : a 27 ∈ [0,7] := remove (a 27) 1 [0,1,7] d27 b2
  have b3 : a 27 ≠ 7 := exclude [0,3] (fun u v => edge r59 v u) (a 27) (a 19) 7 d19 c59 (by decide +kernel)
  have t3 : a 27 ∈ [0] := remove (a 27) 7 [0,7] t2 b3
  have b4 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 2 d21 c63 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,4] := remove (a 23) 2 [0,1,2,4] d23 b4
  have b5 : a 23 ≠ 4 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 4 d21 c63 (by decide +kernel)
  have t5 : a 23 ∈ [0,1] := remove (a 23) 4 [0,1,4] t4 b5
  have b6 : a 30 ≠ 1 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,6,7,8] := remove (a 30) 1 [0,1,2,6,7,8] d30 b6
  have b7 : a 30 ≠ 7 := exclude [0,1] (fun u v => edge r66 v u) (a 30) (a 22) 7 d22 c66 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,6,8] := remove (a 30) 7 [0,2,6,7,8] t6 b7
  have b8 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 2 t5 c67 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 31) 2 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d31 b8
  have b9 : a 31 ≠ 3 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 3 t5 c67 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 31) 3 [0,1,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 6 t5 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 31) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 7 t5 c67 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 31) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 31 ≠ 10 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 10 t5 c67 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,8,9,11,12,13,14,15,16,17,18,19] := remove (a 31) 10 [0,1,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 31 ≠ 11 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 11 t5 c67 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,8,9,12,13,14,15,16,17,18,19] := remove (a 31) 11 [0,1,8,9,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 31 ≠ 12 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 12 t5 c67 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,8,9,13,14,15,16,17,18,19] := remove (a 31) 12 [0,1,8,9,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 31 ≠ 13 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 13 t5 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,8,9,14,15,16,17,18,19] := remove (a 31) 13 [0,1,8,9,13,14,15,16,17,18,19] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (t15))))

theorem chunk13 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,8,9,14,15,16,17,18,19])
    (d23 : a 23 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,3,5,7,9])
    (d24 : a 24 ∈ [0,6])
    (d26 : a 26 ∈ [0,1,12,13,20,22])
    (d27 : a 27 ∈ [0])
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 31 ∈ [0,1,17] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0,12] := by
  have b0 : a 31 ≠ 14 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 14 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,8,9,15,16,17,18,19] := remove (a 31) 14 [0,1,8,9,14,15,16,17,18,19] d31 b0
  have b1 : a 31 ≠ 15 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 15 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,8,9,16,17,18,19] := remove (a 31) 15 [0,1,8,9,15,16,17,18,19] t0 b1
  have b2 : a 31 ≠ 18 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 18 d23 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,8,9,16,17,19] := remove (a 31) 18 [0,1,8,9,16,17,18,19] t1 b2
  have b3 : a 31 ≠ 19 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 19 d23 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,8,9,16,17] := remove (a 31) 19 [0,1,8,9,16,17,19] t2 b3
  have b4 : a 25 ≠ 1 := exclude [0,6] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t4 : a 25 ∈ [0,3,5,7,9] := remove (a 25) 1 [0,1,3,5,7,9] d25 b4
  have b5 : a 25 ≠ 3 := exclude [0,6] (fun u v => edge r68 v u) (a 25) (a 24) 3 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,5,7,9] := remove (a 25) 3 [0,3,5,7,9] t4 b5
  have b6 : a 25 ≠ 5 := exclude [0,6] (fun u v => edge r68 v u) (a 25) (a 24) 5 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,7,9] := remove (a 25) 5 [0,5,7,9] t5 b6
  have b7 : a 25 ≠ 7 := exclude [0,6] (fun u v => edge r68 v u) (a 25) (a 24) 7 d24 c68 (by decide +kernel)
  have t7 : a 25 ∈ [0,9] := remove (a 25) 7 [0,7,9] t6 b7
  have b8 : a 25 ≠ 9 := exclude [0,6] (fun u v => edge r68 v u) (a 25) (a 24) 9 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [0] := remove (a 25) 9 [0,9] t7 b8
  have b9 : a 26 ≠ 20 := exclude [0,6] (fun u v => edge r69 v u) (a 26) (a 24) 20 d24 c69 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,12,13,22] := remove (a 26) 20 [0,1,12,13,20,22] d26 b9
  have b10 : a 26 ≠ 22 := exclude [0,6] (fun u v => edge r69 v u) (a 26) (a 24) 22 d24 c69 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,12,13] := remove (a 26) 22 [0,1,12,13,22] t9 b10
  have b11 : a 26 ≠ 1 := exclude [0] (edge r73) (a 26) (a 27) 1 d27 c73 (by decide +kernel)
  have t11 : a 26 ∈ [0,12,13] := remove (a 26) 1 [0,1,12,13] t10 b11
  have b12 : a 26 ≠ 13 := exclude [0] (edge r73) (a 26) (a 27) 13 d27 c73 (by decide +kernel)
  have t12 : a 26 ∈ [0,12] := remove (a 26) 13 [0,12,13] t11 b12
  have b13 : a 31 ≠ 8 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 8 d27 c75 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,9,16,17] := remove (a 31) 8 [0,1,8,9,16,17] t3 b13
  have b14 : a 31 ≠ 9 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 9 d27 c75 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,16,17] := remove (a 31) 9 [0,1,9,16,17] t13 b14
  have b15 : a 31 ≠ 16 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 16 d27 c75 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,17] := remove (a 31) 16 [0,1,16,17] t14 b15
  exact And.intro t15 (And.intro t8 (t12))

theorem chunk14 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,17])
    (d27 : a 27 ∈ [0])
    (d28 : a 28 ∈ [0,2,12,18])
    (d29 : a 29 ∈ [0,1,3,15])
    (d30 : a 30 ∈ [0,2,6,8])
    (d6 : a 6 ∈ [0,1,3,5])
    (d14 : a 14 ∈ [0,2])
    (d7 : a 7 ∈ [0,1,2,4])
    (d15 : a 15 ∈ [0,1])
    (d2 : a 2 ∈ [0,1,2])
    (d4 : a 4 ∈ [0,1,3,5])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 31 ∈ [0,1] ∧ a 28 ∈ [0,2] ∧ a 30 ∈ [0,6] ∧ a 29 ∈ [0,1] ∧ a 6 ∈ [0,1] ∧ a 7 ∈ [0,1] ∧ a 2 ∈ [0] ∧ a 4 ∈ [0,1] := by
  have b0 : a 31 ≠ 17 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 17 d27 c75 (by decide +kernel)
  have t0 : a 31 ∈ [0,1] := remove (a 31) 17 [0,1,17] d31 b0
  have b1 : a 28 ≠ 12 := exclude [0,1,3,15] (edge r76) (a 28) (a 29) 12 d29 c76 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,18] := remove (a 28) 12 [0,2,12,18] d28 b1
  have b2 : a 28 ≠ 18 := exclude [0,1,3,15] (edge r76) (a 28) (a 29) 18 d29 c76 (by decide +kernel)
  have t2 : a 28 ∈ [0,2] := remove (a 28) 18 [0,2,18] t1 b2
  have b3 : a 30 ≠ 2 := exclude [0,2] (fun u v => edge r77 v u) (a 30) (a 28) 2 t2 c77 (by decide +kernel)
  have t3 : a 30 ∈ [0,6,8] := remove (a 30) 2 [0,2,6,8] d30 b3
  have b4 : a 30 ≠ 8 := exclude [0,2] (fun u v => edge r77 v u) (a 30) (a 28) 8 t2 c77 (by decide +kernel)
  have t4 : a 30 ∈ [0,6] := remove (a 30) 8 [0,6,8] t3 b4
  have b5 : a 29 ≠ 3 := exclude [0,1] (edge r78) (a 29) (a 31) 3 t0 c78 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,15] := remove (a 29) 3 [0,1,3,15] d29 b5
  have b6 : a 29 ≠ 15 := exclude [0,1] (edge r78) (a 29) (a 31) 15 t0 c78 (by decide +kernel)
  have t6 : a 29 ∈ [0,1] := remove (a 29) 15 [0,1,15] t5 b6
  have b7 : a 6 ≠ 3 := exclude [0,2] (edge r24) (a 6) (a 14) 3 d14 c24 (by decide +kernel)
  have t7 : a 6 ∈ [0,1,5] := remove (a 6) 3 [0,1,3,5] d6 b7
  have b8 : a 6 ≠ 5 := exclude [0,2] (edge r24) (a 6) (a 14) 5 d14 c24 (by decide +kernel)
  have t8 : a 6 ∈ [0,1] := remove (a 6) 5 [0,1,5] t7 b8
  have b9 : a 7 ≠ 2 := exclude [0,1] (edge r26) (a 7) (a 15) 2 d15 c26 (by decide +kernel)
  have t9 : a 7 ∈ [0,1,4] := remove (a 7) 2 [0,1,2,4] d7 b9
  have b10 : a 7 ≠ 4 := exclude [0,1] (edge r26) (a 7) (a 15) 4 d15 c26 (by decide +kernel)
  have t10 : a 7 ∈ [0,1] := remove (a 7) 4 [0,1,4] t9 b10
  have b11 : a 2 ≠ 1 := exclude [0,1] (edge r10) (a 2) (a 6) 1 t8 c10 (by decide +kernel)
  have t11 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b11
  have b12 : a 2 ≠ 2 := exclude [0,1] (edge r10) (a 2) (a 6) 2 t8 c10 (by decide +kernel)
  have t12 : a 2 ∈ [0] := remove (a 2) 2 [0,2] t11 b12
  have b13 : a 4 ≠ 3 := exclude [0,1] (edge r17) (a 4) (a 6) 3 t8 c17 (by decide +kernel)
  have t13 : a 4 ∈ [0,1,5] := remove (a 4) 3 [0,1,3,5] d4 b13
  have b14 : a 4 ≠ 5 := exclude [0,1] (edge r17) (a 4) (a 6) 5 t8 c17 (by decide +kernel)
  have t14 : a 4 ∈ [0,1] := remove (a 4) 5 [0,1,5] t13 b14
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (t14)))))))

theorem chunk15 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,3])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d7 : a 7 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d22 : a 22 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d10 : a 10 ∈ [0,1])
    (d24 : a 24 ∈ [0,6])
    (d11 : a 11 ∈ [0,4])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 7 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 24 ∈ [0] ∧ a 11 ∈ [0] := by
  have b0 : a 5 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 3 [0,3] d5 b0
  have b1 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b1
  have b2 : a 4 ≠ 1 := exclude [0] (edge r16) (a 4) (a 5) 1 t0 c16 (by decide +kernel)
  have t2 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b2
  have b3 : a 6 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 1 t2 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b3
  have b4 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 t2 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b4
  have b5 : a 7 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 1 t0 c20 (by decide +kernel)
  have t5 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b5
  have b6 : a 13 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 2 t0 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b6
  have b7 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 t0 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b7
  have b8 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 t3 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b8
  have b9 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 t3 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b9
  have b10 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 t5 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b10
  have b11 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 t5 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b11
  have b12 : a 8 ≠ 2 := exclude [0] (edge r28) (a 8) (a 9) 2 t1 c28 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b12
  have b13 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 t12 c29 (by decide +kernel)
  have t13 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b13
  have b14 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 t12 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0] := remove (a 24) 6 [0,6] d24 b14
  have b15 : a 11 ≠ 4 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 4 t1 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0] := remove (a 11) 4 [0,4] d11 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_196
