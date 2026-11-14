import PartitionData205_169
namespace PartitionCover205_169
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d1 : a 1 ∈ [0])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    : a 4 ∈ [0,3,4,7] ∧ a 8 ∈ [0,1,4,5] ∧ a 16 ∈ [0,1,4,5] ∧ a 5 ∈ [0,1,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5,6,7,8] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8] d4 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,3,4,5,6,7,8] := remove (a 4) 2 [0,2,3,4,5,6,7,8] t0 b1
  have b2 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,3,4,6,7,8] := remove (a 4) 5 [0,3,4,5,6,7,8] t1 b2
  have b3 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,3,4,7,8] := remove (a 4) 6 [0,3,4,6,7,8] t2 b3
  have b4 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,3,4,7] := remove (a 4) 8 [0,3,4,7,8] t3 b4
  have b5 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,3,4,5] := remove (a 8) 2 [0,1,2,3,4,5] d8 b5
  have b6 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,4,5] := remove (a 8) 3 [0,1,3,4,5] t5 b6
  have b7 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,3,4,5] := remove (a 16) 2 [0,1,2,3,4,5] d16 b7
  have b8 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,1,4,5] := remove (a 16) 3 [0,1,3,4,5] t7 b8
  have b9 : a 5 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t9 : a 5 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d5 b9
  have b10 : a 5 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t10 : a 5 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 5 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 5 ≠ 5 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 5 ≠ 6 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 6 d1 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 5 ≠ 7 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 7 d1 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 5 ≠ 8 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 8 d1 c6 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 5) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t4 (And.intro t6 (And.intro t8 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,9,10,11,12,13,14,15,16,17])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (d2 : a 2 ∈ [0])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 5 ∈ [0,1,12,13] ∧ a 9 ∈ [0,5] ∧ a 17 ∈ [0,5] ∧ a 6 ∈ [0,2,3,4,5,6,7,8] := by
  have b0 : a 5 ≠ 9 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 9 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 5) 9 [0,1,9,10,11,12,13,14,15,16,17] d5 b0
  have b1 : a 5 ≠ 10 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 10 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 5) 10 [0,1,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 5 ≠ 11 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 11 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,1,12,13,14,15,16,17] := remove (a 5) 11 [0,1,11,12,13,14,15,16,17] t1 b2
  have b3 : a 5 ≠ 14 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 14 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,1,12,13,15,16,17] := remove (a 5) 14 [0,1,12,13,14,15,16,17] t2 b3
  have b4 : a 5 ≠ 15 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 15 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,1,12,13,16,17] := remove (a 5) 15 [0,1,12,13,15,16,17] t3 b4
  have b5 : a 5 ≠ 16 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 16 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,1,12,13,17] := remove (a 5) 16 [0,1,12,13,16,17] t4 b5
  have b6 : a 5 ≠ 17 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 17 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,1,12,13] := remove (a 5) 17 [0,1,12,13,17] t5 b6
  have b7 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t7 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b7
  have b8 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,3,4,5] := remove (a 9) 2 [0,2,3,4,5] t7 b8
  have b9 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,4,5] := remove (a 9) 3 [0,3,4,5] t8 b9
  have b10 : a 9 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,5] := remove (a 9) 4 [0,4,5] t9 b10
  have b11 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t11 : a 17 ∈ [0,2,3,4,5] := remove (a 17) 1 [0,1,2,3,4,5] d17 b11
  have b12 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t12 : a 17 ∈ [0,3,4,5] := remove (a 17) 2 [0,2,3,4,5] t11 b12
  have b13 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t13 : a 17 ∈ [0,4,5] := remove (a 17) 3 [0,3,4,5] t12 b13
  have b14 : a 17 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t14 : a 17 ∈ [0,5] := remove (a 17) 4 [0,4,5] t13 b14
  have b15 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,2,3,4,5,6,7,8] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8] d6 b15
  exact And.intro t6 (And.intro t10 (And.intro t14 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,2,3,4,5,6,7,8])
    (d2 : a 2 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0])
    (d4 : a 4 ∈ [0,3,4,7])
    (d5 : a 5 ∈ [0,1,12,13])
    (d12 : a 12 ∈ [0,1,2])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 6 ∈ [0,2,4,8] ∧ a 19 ∈ [0,2] ∧ a 4 ∈ [0,7] ∧ a 5 ∈ [0,13] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,2,4,5,6,7,8] := remove (a 6) 3 [0,2,3,4,5,6,7,8] d6 b0
  have b1 : a 6 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,4,5,7,8] := remove (a 6) 6 [0,2,4,5,6,7,8] t0 b1
  have b2 : a 19 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b2
  have b3 : a 19 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,2,4,5] := remove (a 19) 3 [0,2,3,4,5] t2 b3
  have b4 : a 19 ≠ 4 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,2,5] := remove (a 19) 4 [0,2,4,5] t3 b4
  have b5 : a 19 ≠ 5 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,2] := remove (a 19) 5 [0,2,5] t4 b5
  have b6 : a 4 ≠ 3 := exclude [0,1,12,13] (edge r16) (a 4) (a 5) 3 d5 c16 (by decide +kernel)
  have t6 : a 4 ∈ [0,4,7] := remove (a 4) 3 [0,3,4,7] d4 b6
  have b7 : a 4 ≠ 4 := exclude [0,1,12,13] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t7 : a 4 ∈ [0,7] := remove (a 4) 4 [0,4,7] t6 b7
  have b8 : a 5 ≠ 1 := exclude [0,7] (fun u v => edge r16 v u) (a 5) (a 4) 1 t7 c16 (by decide +kernel)
  have t8 : a 5 ∈ [0,12,13] := remove (a 5) 1 [0,1,12,13] d5 b8
  have b9 : a 5 ≠ 12 := exclude [0,7] (fun u v => edge r16 v u) (a 5) (a 4) 12 t7 c16 (by decide +kernel)
  have t9 : a 5 ∈ [0,13] := remove (a 5) 12 [0,12,13] t8 b9
  have b10 : a 6 ≠ 5 := exclude [0,7] (fun u v => edge r17 v u) (a 6) (a 4) 5 t7 c17 (by decide +kernel)
  have t10 : a 6 ∈ [0,2,4,7,8] := remove (a 6) 5 [0,2,4,5,7,8] t1 b10
  have b11 : a 6 ≠ 7 := exclude [0,7] (fun u v => edge r17 v u) (a 6) (a 4) 7 t7 c17 (by decide +kernel)
  have t11 : a 6 ∈ [0,2,4,8] := remove (a 6) 7 [0,2,4,7,8] t10 b11
  have b12 : a 12 ≠ 1 := exclude [0,7] (fun u v => edge r18 v u) (a 12) (a 4) 1 t7 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,2] := remove (a 12) 1 [0,1,2] d12 b12
  have b13 : a 12 ≠ 2 := exclude [0,7] (fun u v => edge r18 v u) (a 12) (a 4) 2 t7 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0] := remove (a 12) 2 [0,2] t12 b13
  have b14 : a 20 ≠ 1 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 1 t7 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d20 b14
  have b15 : a 20 ≠ 2 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 2 t7 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t11 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d4 : a 4 ∈ [0,7])
    (d7 : a 7 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,13])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 20 ∈ [0,3,4,5,8,11,16,17] ∧ a 7 ∈ [0,2] ∧ a 21 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 20 ≠ 6 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 6 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d20 b0
  have b1 : a 20 ≠ 7 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 7 [0,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 20 ≠ 9 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,3,4,5,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 9 [0,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 20 ≠ 10 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,3,4,5,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 10 [0,3,4,5,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 20 ≠ 12 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 12 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,3,4,5,8,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 12 [0,3,4,5,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 20 ≠ 13 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 13 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,3,4,5,8,11,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 13 [0,3,4,5,8,11,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 20 ≠ 14 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 14 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,3,4,5,8,11,15,16,17,18,19,20,21,22,23] := remove (a 20) 14 [0,3,4,5,8,11,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 20 ≠ 15 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 15 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,3,4,5,8,11,16,17,18,19,20,21,22,23] := remove (a 20) 15 [0,3,4,5,8,11,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 20 ≠ 18 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 18 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,3,4,5,8,11,16,17,19,20,21,22,23] := remove (a 20) 18 [0,3,4,5,8,11,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 20 ≠ 19 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 19 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,3,4,5,8,11,16,17,20,21,22,23] := remove (a 20) 19 [0,3,4,5,8,11,16,17,19,20,21,22,23] t8 b9
  have b10 : a 20 ≠ 20 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 20 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,3,4,5,8,11,16,17,21,22,23] := remove (a 20) 20 [0,3,4,5,8,11,16,17,20,21,22,23] t9 b10
  have b11 : a 20 ≠ 21 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 21 d4 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,3,4,5,8,11,16,17,22,23] := remove (a 20) 21 [0,3,4,5,8,11,16,17,21,22,23] t10 b11
  have b12 : a 20 ≠ 22 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 22 d4 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,3,4,5,8,11,16,17,23] := remove (a 20) 22 [0,3,4,5,8,11,16,17,22,23] t11 b12
  have b13 : a 20 ≠ 23 := exclude [0,7] (fun u v => edge r19 v u) (a 20) (a 4) 23 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,3,4,5,8,11,16,17] := remove (a 20) 23 [0,3,4,5,8,11,16,17,23] t12 b13
  have b14 : a 7 ≠ 1 := exclude [0,13] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t14 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b14
  have b15 : a 21 ≠ 1 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t15 : a 21 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d21 b15
  exact And.intro t13 (And.intro t14 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_169
