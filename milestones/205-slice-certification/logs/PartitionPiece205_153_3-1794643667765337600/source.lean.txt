import PartitionData205_153
namespace PartitionCover205_153
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,18,19,20,21,22,23,24,25,26,27])
    (d7 : a 7 ∈ [0,12])
    (d9 : a 9 ∈ [0,2,4,6])
    (d8 : a 8 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,3])
    (d11 : a 11 ∈ [0,2,5,7])
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    : a 15 ∈ [0,1] ∧ a 9 ∈ [0,2] ∧ a 8 ∈ [0,1] ∧ a 11 ∈ [0,2] := by
  have b0 : a 15 ≠ 18 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 18 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,19,20,21,22,23,24,25,26,27] := remove (a 15) 18 [0,1,18,19,20,21,22,23,24,25,26,27] d15 b0
  have b1 : a 15 ≠ 19 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 19 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,20,21,22,23,24,25,26,27] := remove (a 15) 19 [0,1,19,20,21,22,23,24,25,26,27] t0 b1
  have b2 : a 15 ≠ 20 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 20 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,21,22,23,24,25,26,27] := remove (a 15) 20 [0,1,20,21,22,23,24,25,26,27] t1 b2
  have b3 : a 15 ≠ 21 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 21 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,22,23,24,25,26,27] := remove (a 15) 21 [0,1,21,22,23,24,25,26,27] t2 b3
  have b4 : a 15 ≠ 22 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 22 d7 c19 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,23,24,25,26,27] := remove (a 15) 22 [0,1,22,23,24,25,26,27] t3 b4
  have b5 : a 15 ≠ 23 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 23 d7 c19 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,24,25,26,27] := remove (a 15) 23 [0,1,23,24,25,26,27] t4 b5
  have b6 : a 15 ≠ 24 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 24 d7 c19 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,25,26,27] := remove (a 15) 24 [0,1,24,25,26,27] t5 b6
  have b7 : a 15 ≠ 25 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 25 d7 c19 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,26,27] := remove (a 15) 25 [0,1,25,26,27] t6 b7
  have b8 : a 15 ≠ 26 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 26 d7 c19 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,27] := remove (a 15) 26 [0,1,26,27] t7 b8
  have b9 : a 15 ≠ 27 := exclude [0,12] (fun u v => edge r19 v u) (a 15) (a 7) 27 d7 c19 (by decide +kernel)
  have t9 : a 15 ∈ [0,1] := remove (a 15) 27 [0,1,27] t8 b9
  have b10 : a 9 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r20 v u) (a 9) (a 8) 4 d8 c20 (by decide +kernel)
  have t10 : a 9 ∈ [0,2,6] := remove (a 9) 4 [0,2,4,6] d9 b10
  have b11 : a 9 ≠ 6 := exclude [0,1,2,3] (fun u v => edge r20 v u) (a 9) (a 8) 6 d8 c20 (by decide +kernel)
  have t11 : a 9 ∈ [0,2] := remove (a 9) 6 [0,2,6] t10 b11
  have b12 : a 8 ≠ 2 := exclude [0,3] (edge r22) (a 8) (a 12) 2 d12 c22 (by decide +kernel)
  have t12 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b12
  have b13 : a 8 ≠ 3 := exclude [0,3] (edge r22) (a 8) (a 12) 3 d12 c22 (by decide +kernel)
  have t13 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t12 b13
  have b14 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r23 v u) (a 11) (a 9) 5 t11 c23 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,7] := remove (a 11) 5 [0,2,5,7] d11 b14
  have b15 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r23 v u) (a 11) (a 9) 7 t11 c23 (by decide +kernel)
  have t15 : a 11 ∈ [0,2] := remove (a 11) 7 [0,2,7] t14 b15
  exact And.intro t9 (And.intro t11 (And.intro t13 (t15)))

theorem chunk13 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,3,4,6,7,9,10])
    (d12 : a 12 ∈ [0,3])
    (d1 : a 1 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,12])
    (d2 : a 2 ∈ [0,1,2])
    (d6 : a 6 ∈ [0,1])
    (d3 : a 3 ∈ [0,2,5,7])
    (d7 : a 7 ∈ [0,12])
    (c5 : edge r5 (a 1) (a 5)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    (c29 : edge r29 (a 12) (a 14)=true)
    : a 10 ∈ [0,1] ∧ a 14 ∈ [0,3] ∧ a 1 ∈ [0,1] ∧ a 2 ∈ [0] ∧ a 3 ∈ [0,2] := by
  have b0 : a 10 ≠ 2 := exclude [0,2] (edge r25) (a 10) (a 11) 2 d11 c25 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,3] := remove (a 10) 2 [0,1,2,3] d10 b0
  have b1 : a 10 ≠ 3 := exclude [0,2] (edge r25) (a 10) (a 11) 3 d11 c25 (by decide +kernel)
  have t1 : a 10 ∈ [0,1] := remove (a 10) 3 [0,1,3] t0 b1
  have b2 : a 14 ≠ 6 := exclude [0,1] (fun u v => edge r26 v u) (a 14) (a 10) 6 t1 c26 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,3,4,7,9,10] := remove (a 14) 6 [0,1,3,4,6,7,9,10] d14 b2
  have b3 : a 14 ≠ 7 := exclude [0,1] (fun u v => edge r26 v u) (a 14) (a 10) 7 t1 c26 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,3,4,9,10] := remove (a 14) 7 [0,1,3,4,7,9,10] t2 b3
  have b4 : a 14 ≠ 9 := exclude [0,1] (fun u v => edge r26 v u) (a 14) (a 10) 9 t1 c26 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,3,4,10] := remove (a 14) 9 [0,1,3,4,9,10] t3 b4
  have b5 : a 14 ≠ 10 := exclude [0,1] (fun u v => edge r26 v u) (a 14) (a 10) 10 t1 c26 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,3,4] := remove (a 14) 10 [0,1,3,4,10] t4 b5
  have b6 : a 14 ≠ 1 := exclude [0,3] (fun u v => edge r29 v u) (a 14) (a 12) 1 d12 c29 (by decide +kernel)
  have t6 : a 14 ∈ [0,3,4] := remove (a 14) 1 [0,1,3,4] t5 b6
  have b7 : a 14 ≠ 4 := exclude [0,3] (fun u v => edge r29 v u) (a 14) (a 12) 4 d12 c29 (by decide +kernel)
  have t7 : a 14 ∈ [0,3] := remove (a 14) 4 [0,3,4] t6 b7
  have b8 : a 1 ≠ 2 := exclude [0,12] (edge r5) (a 1) (a 5) 2 d5 c5 (by decide +kernel)
  have t8 : a 1 ∈ [0,1,3] := remove (a 1) 2 [0,1,2,3] d1 b8
  have b9 : a 1 ≠ 3 := exclude [0,12] (edge r5) (a 1) (a 5) 3 d5 c5 (by decide +kernel)
  have t9 : a 1 ∈ [0,1] := remove (a 1) 3 [0,1,3] t8 b9
  have b10 : a 2 ≠ 1 := exclude [0,1] (edge r8) (a 2) (a 6) 1 d6 c8 (by decide +kernel)
  have t10 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b10
  have b11 : a 2 ≠ 2 := exclude [0,1] (edge r8) (a 2) (a 6) 2 d6 c8 (by decide +kernel)
  have t11 : a 2 ∈ [0] := remove (a 2) 2 [0,2] t10 b11
  have b12 : a 3 ≠ 5 := exclude [0,12] (edge r10) (a 3) (a 7) 5 d7 c10 (by decide +kernel)
  have t12 : a 3 ∈ [0,2,7] := remove (a 3) 5 [0,2,5,7] d3 b12
  have b13 : a 3 ≠ 7 := exclude [0,12] (edge r10) (a 3) (a 7) 7 d7 c10 (by decide +kernel)
  have t13 : a 3 ∈ [0,2] := remove (a 3) 7 [0,2,7] t12 b13
  exact And.intro t1 (And.intro t7 (And.intro t9 (And.intro t11 (t13))))

theorem chunk14 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,12])
    (d9 : a 9 ∈ [0,2])
    (d7 : a 7 ∈ [0,12])
    (d11 : a 11 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,3])
    (d13 : a 13 ∈ [0,1])
    (d14 : a 14 ∈ [0,3])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 15 ∈ [0] := by
  have b0 : a 3 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 3) (a 1) 2 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b0
  have b1 : a 5 ≠ 12 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 12 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 12 [0,12] d5 b1
  have b2 : a 9 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 2 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b2
  have b3 : a 7 ≠ 12 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 12 t0 c10 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 12 [0,12] d7 b3
  have b4 : a 11 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 2 t0 c11 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b4
  have b5 : a 4 ≠ 1 := exclude [0] (edge r12) (a 4) (a 5) 1 t1 c12 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b5
  have b6 : a 6 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 6) (a 4) 1 t5 c13 (by decide +kernel)
  have t6 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b6
  have b7 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t5 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0] := remove (a 12) 3 [0,3] d12 b7
  have b8 : a 13 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 1 t1 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b8
  have b9 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 t6 c18 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 3 [0,3] d14 b9
  have b10 : a 8 ≠ 1 := exclude [0] (edge r20) (a 8) (a 9) 1 t2 c20 (by decide +kernel)
  have t10 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b10
  have b11 : a 10 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 1 t10 c21 (by decide +kernel)
  have t11 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b11
  have b12 : a 15 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 1 t4 c27 (by decide +kernel)
  have t12 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,12])
    (d9 : a 9 ∈ [0,2])
    (d7 : a 7 ∈ [0,12])
    (d11 : a 11 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,3])
    (d13 : a 13 ∈ [0,1])
    (d14 : a 14 ∈ [0,3])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    : a 3 ∈ [2] ∧ a 5 ∈ [12] ∧ a 9 ∈ [2] ∧ a 7 ∈ [12] ∧ a 11 ∈ [2] ∧ a 4 ∈ [1] ∧ a 6 ∈ [1] ∧ a 12 ∈ [3] ∧ a 13 ∈ [1] ∧ a 14 ∈ [3] ∧ a 8 ∈ [1] ∧ a 10 ∈ [1] ∧ a 15 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r4 v u) (a 3) (a 1) 0 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 5) (a 1) 0 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [12] := remove (a 5) 0 [0,12] d5 b1
  have b2 : a 9 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 9) (a 1) 0 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b2
  have b3 : a 7 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 7) (a 3) 0 t0 c10 (by decide +kernel)
  have t3 : a 7 ∈ [12] := remove (a 7) 0 [0,12] d7 b3
  have b4 : a 11 ≠ 0 := exclude [2] (fun u v => edge r11 v u) (a 11) (a 3) 0 t0 c11 (by decide +kernel)
  have t4 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b4
  have b5 : a 4 ≠ 0 := exclude [12] (edge r12) (a 4) (a 5) 0 t1 c12 (by decide +kernel)
  have t5 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b5
  have b6 : a 6 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 6) (a 4) 0 t5 c13 (by decide +kernel)
  have t6 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b6
  have b7 : a 12 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 12) (a 4) 0 t5 c14 (by decide +kernel)
  have t7 : a 12 ∈ [3] := remove (a 12) 0 [0,3] d12 b7
  have b8 : a 13 ≠ 0 := exclude [12] (fun u v => edge r16 v u) (a 13) (a 5) 0 t1 c16 (by decide +kernel)
  have t8 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b8
  have b9 : a 14 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 14) (a 6) 0 t6 c18 (by decide +kernel)
  have t9 : a 14 ∈ [3] := remove (a 14) 0 [0,3] d14 b9
  have b10 : a 8 ≠ 0 := exclude [2] (edge r20) (a 8) (a 9) 0 t2 c20 (by decide +kernel)
  have t10 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b10
  have b11 : a 10 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 10) (a 8) 0 t10 c21 (by decide +kernel)
  have t11 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b11
  have b12 : a 15 ≠ 0 := exclude [2] (fun u v => edge r27 v u) (a 15) (a 11) 0 t4 c27 (by decide +kernel)
  have t12 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_153
