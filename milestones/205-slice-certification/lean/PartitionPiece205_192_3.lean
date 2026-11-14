import PartitionData205_192
namespace PartitionCover205_192
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,2,8,10,16,17,18,19,20,21,22,23])
    (d24 : a 24 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    : a 25 ∈ [0,2,8,10] ∧ a 26 ∈ [0,1,6,7,12,13,14,15,16,17] := by
  have b0 : a 25 ≠ 16 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 16 d24 c68 (by decide +kernel)
  have t0 : a 25 ∈ [0,2,8,10,17,18,19,20,21,22,23] := remove (a 25) 16 [0,2,8,10,16,17,18,19,20,21,22,23] d25 b0
  have b1 : a 25 ≠ 17 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 17 d24 c68 (by decide +kernel)
  have t1 : a 25 ∈ [0,2,8,10,18,19,20,21,22,23] := remove (a 25) 17 [0,2,8,10,17,18,19,20,21,22,23] t0 b1
  have b2 : a 25 ≠ 18 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 18 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,8,10,19,20,21,22,23] := remove (a 25) 18 [0,2,8,10,18,19,20,21,22,23] t1 b2
  have b3 : a 25 ≠ 19 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 19 d24 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,8,10,20,21,22,23] := remove (a 25) 19 [0,2,8,10,19,20,21,22,23] t2 b3
  have b4 : a 25 ≠ 20 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 20 d24 c68 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,8,10,21,22,23] := remove (a 25) 20 [0,2,8,10,20,21,22,23] t3 b4
  have b5 : a 25 ≠ 21 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 21 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,8,10,22,23] := remove (a 25) 21 [0,2,8,10,21,22,23] t4 b5
  have b6 : a 25 ≠ 22 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 22 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,8,10,23] := remove (a 25) 22 [0,2,8,10,22,23] t5 b6
  have b7 : a 25 ≠ 23 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 23 d24 c68 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,8,10] := remove (a 25) 23 [0,2,8,10,23] t6 b7
  have b8 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 2 d24 c69 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d26 b8
  have b9 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 3 d24 c69 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 26 ≠ 4 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 4 d24 c69 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 5 d24 c69 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 26 ≠ 8 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 8 d24 c69 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 26) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 26 ≠ 9 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 9 d24 c69 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 26) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 26 ≠ 10 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 10 d24 c69 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 26) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 26 ≠ 11 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 11 d24 c69 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 26) 11 [0,1,6,7,11,12,13,14,15,16,17] t14 b15
  exact And.intro t7 (t15)

theorem chunk13 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,6,7,12,13,14,15,16,17])
    (d24 : a 24 ∈ [0,1])
    (d25 : a 25 ∈ [0,2,8,10])
    (d29 : a 29 ∈ [0,8])
    (d31 : a 31 ∈ [0,1,6,7,10,11])
    (d27 : a 27 ∈ [0,3])
    (d4 : a 4 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,1])
    (d6 : a 6 ∈ [0,2,6,8])
    (d14 : a 14 ∈ [0,4])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 26 ∈ [0,1,6,7] ∧ a 25 ∈ [0,8] ∧ a 31 ∈ [0,6] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0,6] := by
  have b0 : a 26 ≠ 12 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 12 d24 c69 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,6,7,13,14,15,16,17] := remove (a 26) 12 [0,1,6,7,12,13,14,15,16,17] d26 b0
  have b1 : a 26 ≠ 13 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 13 d24 c69 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,6,7,14,15,16,17] := remove (a 26) 13 [0,1,6,7,13,14,15,16,17] t0 b1
  have b2 : a 26 ≠ 14 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 14 d24 c69 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,6,7,15,16,17] := remove (a 26) 14 [0,1,6,7,14,15,16,17] t1 b2
  have b3 : a 26 ≠ 15 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 15 d24 c69 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,6,7,16,17] := remove (a 26) 15 [0,1,6,7,15,16,17] t2 b3
  have b4 : a 26 ≠ 16 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 16 d24 c69 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,6,7,17] := remove (a 26) 16 [0,1,6,7,16,17] t3 b4
  have b5 : a 26 ≠ 17 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 17 d24 c69 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,6,7] := remove (a 26) 17 [0,1,6,7,17] t4 b5
  have b6 : a 25 ≠ 2 := exclude [0,8] (edge r72) (a 25) (a 29) 2 d29 c72 (by decide +kernel)
  have t6 : a 25 ∈ [0,8,10] := remove (a 25) 2 [0,2,8,10] d25 b6
  have b7 : a 25 ≠ 10 := exclude [0,8] (edge r72) (a 25) (a 29) 10 d29 c72 (by decide +kernel)
  have t7 : a 25 ∈ [0,8] := remove (a 25) 10 [0,8,10] t6 b7
  have b8 : a 31 ≠ 10 := exclude [0,3] (fun u v => edge r75 v u) (a 31) (a 27) 10 d27 c75 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,6,7,11] := remove (a 31) 10 [0,1,6,7,10,11] d31 b8
  have b9 : a 31 ≠ 11 := exclude [0,3] (fun u v => edge r75 v u) (a 31) (a 27) 11 d27 c75 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,6,7] := remove (a 31) 11 [0,1,6,7,11] t8 b9
  have b10 : a 31 ≠ 1 := exclude [0,8] (fun u v => edge r78 v u) (a 31) (a 29) 1 d29 c78 (by decide +kernel)
  have t10 : a 31 ∈ [0,6,7] := remove (a 31) 1 [0,1,6,7] t9 b10
  have b11 : a 31 ≠ 7 := exclude [0,8] (fun u v => edge r78 v u) (a 31) (a 29) 7 d29 c78 (by decide +kernel)
  have t11 : a 31 ∈ [0,6] := remove (a 31) 7 [0,6,7] t10 b11
  have b12 : a 4 ≠ 1 := exclude [0,1] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t12 : a 4 ∈ [0,2] := remove (a 4) 1 [0,1,2] d4 b12
  have b13 : a 4 ≠ 2 := exclude [0,1] (edge r18) (a 4) (a 12) 2 d12 c18 (by decide +kernel)
  have t13 : a 4 ∈ [0] := remove (a 4) 2 [0,2] t12 b13
  have b14 : a 6 ≠ 2 := exclude [0,4] (edge r24) (a 6) (a 14) 2 d14 c24 (by decide +kernel)
  have t14 : a 6 ∈ [0,6,8] := remove (a 6) 2 [0,2,6,8] d6 b14
  have b15 : a 6 ≠ 8 := exclude [0,4] (edge r24) (a 6) (a 14) 8 d14 c24 (by decide +kernel)
  have t15 : a 6 ∈ [0,6] := remove (a 6) 8 [0,6,8] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t11 (And.intro t13 (t15))))

theorem chunk14 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2,3,5])
    (d15 : a 15 ∈ [0,6])
    (d24 : a 24 ∈ [0,1])
    (d25 : a 25 ∈ [0,8])
    (d26 : a 26 ∈ [0,1,6,7])
    (d30 : a 30 ∈ [0,1,6,7])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 7 ∈ [0,3] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0,6] ∧ a 30 ∈ [0,6] := by
  have b0 : a 7 ≠ 2 := exclude [0,6] (edge r26) (a 7) (a 15) 2 d15 c26 (by decide +kernel)
  have t0 : a 7 ∈ [0,3,5] := remove (a 7) 2 [0,2,3,5] d7 b0
  have b1 : a 7 ≠ 5 := exclude [0,6] (edge r26) (a 7) (a 15) 5 d15 c26 (by decide +kernel)
  have t1 : a 7 ∈ [0,3] := remove (a 7) 5 [0,3,5] t0 b1
  have b2 : a 24 ≠ 1 := exclude [0,8] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b2
  have b3 : a 26 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 1 t2 c69 (by decide +kernel)
  have t3 : a 26 ∈ [0,6,7] := remove (a 26) 1 [0,1,6,7] d26 b3
  have b4 : a 26 ≠ 7 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 7 t2 c69 (by decide +kernel)
  have t4 : a 26 ∈ [0,6] := remove (a 26) 7 [0,6,7] t3 b4
  have b5 : a 30 ≠ 1 := exclude [0,6] (fun u v => edge r74 v u) (a 30) (a 26) 1 t4 c74 (by decide +kernel)
  have t5 : a 30 ∈ [0,6,7] := remove (a 30) 1 [0,1,6,7] d30 b5
  have b6 : a 30 ≠ 7 := exclude [0,6] (fun u v => edge r74 v u) (a 30) (a 26) 7 t4 c74 (by decide +kernel)
  have t6 : a 30 ∈ [0,6] := remove (a 30) 7 [0,6,7] t5 b6
  exact And.intro t1 (And.intro t2 (And.intro t4 (t6)))

theorem chunk15 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,6])
    (d10 : a 10 ∈ [0,4])
    (d18 : a 18 ∈ [0,1])
    (d7 : a 7 ∈ [0,3])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,4])
    (d21 : a 21 ∈ [0,1])
    (d14 : a 14 ∈ [0,4])
    (d15 : a 15 ∈ [0,6])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d9 : a 9 ∈ [0,4])
    (d28 : a 28 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 3 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 9 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 3 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 2 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b0
  have b1 : a 2 ≠ 2 := exclude [0] (edge r9) (a 2) (a 3) 2 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b1
  have b2 : a 6 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 6 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0] := remove (a 6) 6 [0,6] d6 b2
  have b3 : a 10 ≠ 4 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 4 t1 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0] := remove (a 10) 4 [0,4] d10 b3
  have b4 : a 18 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 1 t1 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b4
  have b5 : a 7 ≠ 3 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 3 t0 c13 (by decide +kernel)
  have t5 : a 7 ∈ [0] := remove (a 7) 3 [0,3] d7 b5
  have b6 : a 5 ≠ 1 := exclude [0] (edge r20) (a 5) (a 7) 1 t5 c20 (by decide +kernel)
  have t6 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b6
  have b7 : a 13 ≠ 4 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 4 t6 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0] := remove (a 13) 4 [0,4] d13 b7
  have b8 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 t6 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b8
  have b9 : a 14 ≠ 4 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 4 t2 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 4 [0,4] d14 b9
  have b10 : a 15 ≠ 6 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 6 t5 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 6 [0,6] d15 b10
  have b11 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 t5 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b11
  have b12 : a 8 ≠ 2 := exclude [0] (edge r29) (a 8) (a 10) 2 t3 c29 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b12
  have b13 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 t12 c30 (by decide +kernel)
  have t13 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b13
  have b14 : a 9 ≠ 4 := exclude [0] (edge r33) (a 9) (a 13) 4 t7 c33 (by decide +kernel)
  have t14 : a 9 ∈ [0] := remove (a 9) 4 [0,4] d9 b14
  have b15 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t13 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_192
