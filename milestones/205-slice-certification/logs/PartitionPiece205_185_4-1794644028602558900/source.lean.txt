import PartitionData205_185
namespace PartitionCover205_185
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,6])
    (d22 : a 22 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,4,5,6,7,9])
    (d28 : a 28 ∈ [0,4,5,8,10,11,14,19])
    (d24 : a 24 ∈ [0,4])
    (d30 : a 30 ∈ [0,3,4,5])
    (d26 : a 26 ∈ [0,10])
    (d3 : a 3 ∈ [0,2,6,8,12,13,14,16])
    (d1 : a 1 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 23 ∈ [0,1] ∧ a 31 ∈ [0,6] ∧ a 28 ∈ [0,14] ∧ a 30 ∈ [0,4] ∧ a 3 ∈ [0,2,6,8,14,16] := by
  have b0 : a 23 ≠ 6 := exclude [0,1] (fun u v => edge r65 v u) (a 23) (a 22) 6 d22 c65 (by decide +kernel)
  have t0 : a 23 ∈ [0,1] := remove (a 23) 6 [0,1,6] d23 b0
  have b1 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 1 t0 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0,4,5,6,7,9] := remove (a 31) 1 [0,1,4,5,6,7,9] d31 b1
  have b2 : a 31 ≠ 4 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 4 t0 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0,5,6,7,9] := remove (a 31) 4 [0,4,5,6,7,9] t1 b2
  have b3 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 5 t0 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,6,7,9] := remove (a 31) 5 [0,5,6,7,9] t2 b3
  have b4 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 7 t0 c67 (by decide +kernel)
  have t4 : a 31 ∈ [0,6,9] := remove (a 31) 7 [0,6,7,9] t3 b4
  have b5 : a 31 ≠ 9 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 9 t0 c67 (by decide +kernel)
  have t5 : a 31 ∈ [0,6] := remove (a 31) 9 [0,6,9] t4 b5
  have b6 : a 28 ≠ 4 := exclude [0,4] (fun u v => edge r70 v u) (a 28) (a 24) 4 d24 c70 (by decide +kernel)
  have t6 : a 28 ∈ [0,5,8,10,11,14,19] := remove (a 28) 4 [0,4,5,8,10,11,14,19] d28 b6
  have b7 : a 28 ≠ 5 := exclude [0,4] (fun u v => edge r70 v u) (a 28) (a 24) 5 d24 c70 (by decide +kernel)
  have t7 : a 28 ∈ [0,8,10,11,14,19] := remove (a 28) 5 [0,5,8,10,11,14,19] t6 b7
  have b8 : a 28 ≠ 8 := exclude [0,4] (fun u v => edge r70 v u) (a 28) (a 24) 8 d24 c70 (by decide +kernel)
  have t8 : a 28 ∈ [0,10,11,14,19] := remove (a 28) 8 [0,8,10,11,14,19] t7 b8
  have b9 : a 28 ≠ 10 := exclude [0,4] (fun u v => edge r70 v u) (a 28) (a 24) 10 d24 c70 (by decide +kernel)
  have t9 : a 28 ∈ [0,11,14,19] := remove (a 28) 10 [0,10,11,14,19] t8 b9
  have b10 : a 28 ≠ 11 := exclude [0,4] (fun u v => edge r70 v u) (a 28) (a 24) 11 d24 c70 (by decide +kernel)
  have t10 : a 28 ∈ [0,14,19] := remove (a 28) 11 [0,11,14,19] t9 b10
  have b11 : a 28 ≠ 19 := exclude [0,4] (fun u v => edge r70 v u) (a 28) (a 24) 19 d24 c70 (by decide +kernel)
  have t11 : a 28 ∈ [0,14] := remove (a 28) 19 [0,14,19] t10 b11
  have b12 : a 30 ≠ 3 := exclude [0,10] (fun u v => edge r74 v u) (a 30) (a 26) 3 d26 c74 (by decide +kernel)
  have t12 : a 30 ∈ [0,4,5] := remove (a 30) 3 [0,3,4,5] d30 b12
  have b13 : a 30 ≠ 5 := exclude [0,10] (fun u v => edge r74 v u) (a 30) (a 26) 5 d26 c74 (by decide +kernel)
  have t13 : a 30 ∈ [0,4] := remove (a 30) 5 [0,4,5] t12 b13
  have b14 : a 3 ≠ 12 := exclude [0,1] (fun u v => edge r5 v u) (a 3) (a 1) 12 d1 c5 (by decide +kernel)
  have t14 : a 3 ∈ [0,2,6,8,13,14,16] := remove (a 3) 12 [0,2,6,8,12,13,14,16] d3 b14
  have b15 : a 3 ≠ 13 := exclude [0,1] (fun u v => edge r5 v u) (a 3) (a 1) 13 d1 c5 (by decide +kernel)
  have t15 : a 3 ∈ [0,2,6,8,14,16] := remove (a 3) 13 [0,2,6,8,13,14,16] t14 b15
  exact And.intro t0 (And.intro t5 (And.intro t11 (And.intro t13 (t15))))

theorem chunk17 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2,6,8,14,16])
    (d1 : a 1 ∈ [0,1])
    (d5 : a 5 ∈ [0,3,4,5,6,7,9,10,12,13,14,15,17,18])
    (d2 : a 2 ∈ [0,2,6,8,12,13,14,16])
    (d6 : a 6 ∈ [0,2,3,4,5,6,9,11,13,15,17,19,20,21,22,23])
    (d18 : a 18 ∈ [0,3])
    (d7 : a 7 ∈ [0,1,2,3,5,7,9,10,11])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    : a 3 ∈ [0,2,6,8] ∧ a 5 ∈ [0,3,4,5,6,7,9,12,13,14,15,17] ∧ a 2 ∈ [0,6] ∧ a 6 ∈ [0,2,3,4,6,9,15,17,19,20,21,23] ∧ a 7 ∈ [0,2,5,7,9,10,11] := by
  have b0 : a 3 ≠ 14 := exclude [0,1] (fun u v => edge r5 v u) (a 3) (a 1) 14 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0,2,6,8,16] := remove (a 3) 14 [0,2,6,8,14,16] d3 b0
  have b1 : a 3 ≠ 16 := exclude [0,1] (fun u v => edge r5 v u) (a 3) (a 1) 16 d1 c5 (by decide +kernel)
  have t1 : a 3 ∈ [0,2,6,8] := remove (a 3) 16 [0,2,6,8,16] t0 b1
  have b2 : a 5 ≠ 10 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 10 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,3,4,5,6,7,9,12,13,14,15,17,18] := remove (a 5) 10 [0,3,4,5,6,7,9,10,12,13,14,15,17,18] d5 b2
  have b3 : a 5 ≠ 18 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 18 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,3,4,5,6,7,9,12,13,14,15,17] := remove (a 5) 18 [0,3,4,5,6,7,9,12,13,14,15,17,18] t2 b3
  have b4 : a 2 ≠ 12 := exclude [0,2,6,8] (edge r9) (a 2) (a 3) 12 t1 c9 (by decide +kernel)
  have t4 : a 2 ∈ [0,2,6,8,13,14,16] := remove (a 2) 12 [0,2,6,8,12,13,14,16] d2 b4
  have b5 : a 2 ≠ 13 := exclude [0,2,6,8] (edge r9) (a 2) (a 3) 13 t1 c9 (by decide +kernel)
  have t5 : a 2 ∈ [0,2,6,8,14,16] := remove (a 2) 13 [0,2,6,8,13,14,16] t4 b5
  have b6 : a 2 ≠ 14 := exclude [0,2,6,8] (edge r9) (a 2) (a 3) 14 t1 c9 (by decide +kernel)
  have t6 : a 2 ∈ [0,2,6,8,16] := remove (a 2) 14 [0,2,6,8,14,16] t5 b6
  have b7 : a 2 ≠ 16 := exclude [0,2,6,8] (edge r9) (a 2) (a 3) 16 t1 c9 (by decide +kernel)
  have t7 : a 2 ∈ [0,2,6,8] := remove (a 2) 16 [0,2,6,8,16] t6 b7
  have b8 : a 6 ≠ 5 := exclude [0,2,6,8] (fun u v => edge r10 v u) (a 6) (a 2) 5 t7 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,2,3,4,6,9,11,13,15,17,19,20,21,22,23] := remove (a 6) 5 [0,2,3,4,5,6,9,11,13,15,17,19,20,21,22,23] d6 b8
  have b9 : a 6 ≠ 11 := exclude [0,2,6,8] (fun u v => edge r10 v u) (a 6) (a 2) 11 t7 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,2,3,4,6,9,13,15,17,19,20,21,22,23] := remove (a 6) 11 [0,2,3,4,6,9,11,13,15,17,19,20,21,22,23] t8 b9
  have b10 : a 6 ≠ 13 := exclude [0,2,6,8] (fun u v => edge r10 v u) (a 6) (a 2) 13 t7 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,2,3,4,6,9,15,17,19,20,21,22,23] := remove (a 6) 13 [0,2,3,4,6,9,13,15,17,19,20,21,22,23] t9 b10
  have b11 : a 6 ≠ 22 := exclude [0,2,6,8] (fun u v => edge r10 v u) (a 6) (a 2) 22 t7 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,2,3,4,6,9,15,17,19,20,21,23] := remove (a 6) 22 [0,2,3,4,6,9,15,17,19,20,21,22,23] t10 b11
  have b12 : a 2 ≠ 2 := exclude [0,3] (edge r12) (a 2) (a 18) 2 d18 c12 (by decide +kernel)
  have t12 : a 2 ∈ [0,6,8] := remove (a 2) 2 [0,2,6,8] t7 b12
  have b13 : a 2 ≠ 8 := exclude [0,3] (edge r12) (a 2) (a 18) 8 d18 c12 (by decide +kernel)
  have t13 : a 2 ∈ [0,6] := remove (a 2) 8 [0,6,8] t12 b13
  have b14 : a 7 ≠ 1 := exclude [0,2,6,8] (fun u v => edge r13 v u) (a 7) (a 3) 1 t1 c13 (by decide +kernel)
  have t14 : a 7 ∈ [0,2,3,5,7,9,10,11] := remove (a 7) 1 [0,1,2,3,5,7,9,10,11] d7 b14
  have b15 : a 7 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r13 v u) (a 7) (a 3) 3 t1 c13 (by decide +kernel)
  have t15 : a 7 ∈ [0,2,5,7,9,10,11] := remove (a 7) 3 [0,2,3,5,7,9,10,11] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t13 (And.intro t11 (t15))))

theorem chunk18 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2,5,7,9,10,11])
    (d3 : a 3 ∈ [0,2,6,8])
    (d11 : a 11 ∈ [0,2,18,20])
    (d5 : a 5 ∈ [0,3,4,5,6,7,9,12,13,14,15,17])
    (d13 : a 13 ∈ [0,1,2,23])
    (d21 : a 21 ∈ [0,4])
    (d6 : a 6 ∈ [0,2,3,4,6,9,15,17,19,20,21,23])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    : a 7 ∈ [0,2,7,9,10,11] ∧ a 3 ∈ [0,6] ∧ a 5 ∈ [0,12] ∧ a 6 ∈ [0,4,6,9,15,17,19,21,23] := by
  have b0 : a 7 ≠ 5 := exclude [0,2,6,8] (fun u v => edge r13 v u) (a 7) (a 3) 5 d3 c13 (by decide +kernel)
  have t0 : a 7 ∈ [0,2,7,9,10,11] := remove (a 7) 5 [0,2,5,7,9,10,11] d7 b0
  have b1 : a 3 ≠ 2 := exclude [0,2,18,20] (edge r14) (a 3) (a 11) 2 d11 c14 (by decide +kernel)
  have t1 : a 3 ∈ [0,6,8] := remove (a 3) 2 [0,2,6,8] d3 b1
  have b2 : a 3 ≠ 8 := exclude [0,2,18,20] (edge r14) (a 3) (a 11) 8 d11 c14 (by decide +kernel)
  have t2 : a 3 ∈ [0,6] := remove (a 3) 8 [0,6,8] t1 b2
  have b3 : a 5 ≠ 3 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 3 d13 c21 (by decide +kernel)
  have t3 : a 5 ∈ [0,4,5,6,7,9,12,13,14,15,17] := remove (a 5) 3 [0,3,4,5,6,7,9,12,13,14,15,17] d5 b3
  have b4 : a 5 ≠ 4 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 4 d13 c21 (by decide +kernel)
  have t4 : a 5 ∈ [0,5,6,7,9,12,13,14,15,17] := remove (a 5) 4 [0,4,5,6,7,9,12,13,14,15,17] t3 b4
  have b5 : a 5 ≠ 5 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 5 d13 c21 (by decide +kernel)
  have t5 : a 5 ∈ [0,6,7,9,12,13,14,15,17] := remove (a 5) 5 [0,5,6,7,9,12,13,14,15,17] t4 b5
  have b6 : a 5 ≠ 6 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 6 d13 c21 (by decide +kernel)
  have t6 : a 5 ∈ [0,7,9,12,13,14,15,17] := remove (a 5) 6 [0,6,7,9,12,13,14,15,17] t5 b6
  have b7 : a 5 ≠ 7 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 7 d13 c21 (by decide +kernel)
  have t7 : a 5 ∈ [0,9,12,13,14,15,17] := remove (a 5) 7 [0,7,9,12,13,14,15,17] t6 b7
  have b8 : a 5 ≠ 13 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 13 d13 c21 (by decide +kernel)
  have t8 : a 5 ∈ [0,9,12,14,15,17] := remove (a 5) 13 [0,9,12,13,14,15,17] t7 b8
  have b9 : a 5 ≠ 14 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 14 d13 c21 (by decide +kernel)
  have t9 : a 5 ∈ [0,9,12,15,17] := remove (a 5) 14 [0,9,12,14,15,17] t8 b9
  have b10 : a 5 ≠ 15 := exclude [0,1,2,23] (edge r21) (a 5) (a 13) 15 d13 c21 (by decide +kernel)
  have t10 : a 5 ∈ [0,9,12,17] := remove (a 5) 15 [0,9,12,15,17] t9 b10
  have b11 : a 5 ≠ 9 := exclude [0,4] (edge r22) (a 5) (a 21) 9 d21 c22 (by decide +kernel)
  have t11 : a 5 ∈ [0,12,17] := remove (a 5) 9 [0,9,12,17] t10 b11
  have b12 : a 5 ≠ 17 := exclude [0,4] (edge r22) (a 5) (a 21) 17 d21 c22 (by decide +kernel)
  have t12 : a 5 ∈ [0,12] := remove (a 5) 17 [0,12,17] t11 b12
  have b13 : a 6 ≠ 2 := exclude [0,2,7,9,10,11] (edge r23) (a 6) (a 7) 2 t0 c23 (by decide +kernel)
  have t13 : a 6 ∈ [0,3,4,6,9,15,17,19,20,21,23] := remove (a 6) 2 [0,2,3,4,6,9,15,17,19,20,21,23] d6 b13
  have b14 : a 6 ≠ 3 := exclude [0,2,7,9,10,11] (edge r23) (a 6) (a 7) 3 t0 c23 (by decide +kernel)
  have t14 : a 6 ∈ [0,4,6,9,15,17,19,20,21,23] := remove (a 6) 3 [0,3,4,6,9,15,17,19,20,21,23] t13 b14
  have b15 : a 6 ≠ 20 := exclude [0,2,7,9,10,11] (edge r23) (a 6) (a 7) 20 t0 c23 (by decide +kernel)
  have t15 : a 6 ∈ [0,4,6,9,15,17,19,21,23] := remove (a 6) 20 [0,4,6,9,15,17,19,20,21,23] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t12 (t15)))

theorem chunk19 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,4,6,9,15,17,19,21,23])
    (d7 : a 7 ∈ [0,2,7,9,10,11])
    (d14 : a 14 ∈ [0,4])
    (d23 : a 23 ∈ [0,1])
    (d11 : a 11 ∈ [0,2,18,20])
    (d15 : a 15 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,2,23])
    (d29 : a 29 ∈ [0,4])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,12])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 6 ∈ [0,9] ∧ a 7 ∈ [0,10] ∧ a 11 ∈ [0,18] ∧ a 13 ∈ [0,2] ∧ a 4 ∈ [0,2,3,4,5] := by
  have b0 : a 6 ≠ 21 := exclude [0,2,7,9,10,11] (edge r23) (a 6) (a 7) 21 d7 c23 (by decide +kernel)
  have t0 : a 6 ∈ [0,4,6,9,15,17,19,23] := remove (a 6) 21 [0,4,6,9,15,17,19,21,23] d6 b0
  have b1 : a 7 ≠ 2 := exclude [0,4,6,9,15,17,19,23] (fun u v => edge r23 v u) (a 7) (a 6) 2 t0 c23 (by decide +kernel)
  have t1 : a 7 ∈ [0,7,9,10,11] := remove (a 7) 2 [0,2,7,9,10,11] d7 b1
  have b2 : a 7 ≠ 9 := exclude [0,4,6,9,15,17,19,23] (fun u v => edge r23 v u) (a 7) (a 6) 9 t0 c23 (by decide +kernel)
  have t2 : a 7 ∈ [0,7,10,11] := remove (a 7) 9 [0,7,9,10,11] t1 b2
  have b3 : a 6 ≠ 4 := exclude [0,4] (edge r24) (a 6) (a 14) 4 d14 c24 (by decide +kernel)
  have t3 : a 6 ∈ [0,6,9,15,17,19,23] := remove (a 6) 4 [0,4,6,9,15,17,19,23] t0 b3
  have b4 : a 6 ≠ 6 := exclude [0,4] (edge r24) (a 6) (a 14) 6 d14 c24 (by decide +kernel)
  have t4 : a 6 ∈ [0,9,15,17,19,23] := remove (a 6) 6 [0,6,9,15,17,19,23] t3 b4
  have b5 : a 6 ≠ 15 := exclude [0,4] (edge r24) (a 6) (a 14) 15 d14 c24 (by decide +kernel)
  have t5 : a 6 ∈ [0,9,17,19,23] := remove (a 6) 15 [0,9,15,17,19,23] t4 b5
  have b6 : a 6 ≠ 17 := exclude [0,4] (edge r24) (a 6) (a 14) 17 d14 c24 (by decide +kernel)
  have t6 : a 6 ∈ [0,9,19,23] := remove (a 6) 17 [0,9,17,19,23] t5 b6
  have b7 : a 6 ≠ 19 := exclude [0,4] (edge r24) (a 6) (a 14) 19 d14 c24 (by decide +kernel)
  have t7 : a 6 ∈ [0,9,23] := remove (a 6) 19 [0,9,19,23] t6 b7
  have b8 : a 6 ≠ 23 := exclude [0,4] (edge r24) (a 6) (a 14) 23 d14 c24 (by decide +kernel)
  have t8 : a 6 ∈ [0,9] := remove (a 6) 23 [0,9,23] t7 b8
  have b9 : a 7 ≠ 7 := exclude [0,1] (edge r27) (a 7) (a 23) 7 d23 c27 (by decide +kernel)
  have t9 : a 7 ∈ [0,10,11] := remove (a 7) 7 [0,7,10,11] t2 b9
  have b10 : a 7 ≠ 11 := exclude [0,1] (edge r27) (a 7) (a 23) 11 d23 c27 (by decide +kernel)
  have t10 : a 7 ∈ [0,10] := remove (a 7) 11 [0,10,11] t9 b10
  have b11 : a 11 ≠ 2 := exclude [0,2] (edge r38) (a 11) (a 15) 2 d15 c38 (by decide +kernel)
  have t11 : a 11 ∈ [0,18,20] := remove (a 11) 2 [0,2,18,20] d11 b11
  have b12 : a 11 ≠ 20 := exclude [0,2] (edge r38) (a 11) (a 15) 20 d15 c38 (by decide +kernel)
  have t12 : a 11 ∈ [0,18] := remove (a 11) 20 [0,18,20] t11 b12
  have b13 : a 13 ≠ 1 := exclude [0,4] (edge r44) (a 13) (a 29) 1 d29 c44 (by decide +kernel)
  have t13 : a 13 ∈ [0,2,23] := remove (a 13) 1 [0,1,2,23] d13 b13
  have b14 : a 13 ≠ 23 := exclude [0,4] (edge r44) (a 13) (a 29) 23 d29 c44 (by decide +kernel)
  have t14 : a 13 ∈ [0,2] := remove (a 13) 23 [0,2,23] t13 b14
  have b15 : a 4 ≠ 1 := exclude [0,12] (edge r16) (a 4) (a 5) 1 d5 c16 (by decide +kernel)
  have t15 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b15
  exact And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_185
