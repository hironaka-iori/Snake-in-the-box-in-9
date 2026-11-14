import PartitionData205_175
namespace PartitionCover205_175
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 8 ∈ [0,1,2,5] ∧ a 5 ∈ [0,3] ∧ a 9 ∈ [0,4,12,13,14,15,16,17] := by
  have b0 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,2,4,5] := remove (a 8) 3 [0,1,2,3,4,5] d8 b0
  have b1 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,2,5] := remove (a 8) 4 [0,1,2,4,5] t0 b1
  have b2 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b2
  have b3 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,3,4,5] := remove (a 5) 2 [0,2,3,4,5] t2 b3
  have b4 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,3,5] := remove (a 5) 4 [0,3,4,5] t3 b4
  have b5 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,3] := remove (a 5) 5 [0,3,5] t4 b5
  have b6 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d9 b6
  have b7 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t7 : a 9 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 9 ≠ 6 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 6 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 9 ≠ 7 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,4,8,9,10,11,12,13,14,15,16,17] := remove (a 9) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 9 ≠ 8 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 8 d1 c7 (by decide +kernel)
  have t12 : a 9 ∈ [0,4,9,10,11,12,13,14,15,16,17] := remove (a 9) 8 [0,4,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 9 ≠ 9 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 9 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,4,10,11,12,13,14,15,16,17] := remove (a 9) 9 [0,4,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 9 ≠ 10 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 10 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,4,11,12,13,14,15,16,17] := remove (a 9) 10 [0,4,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 9 ≠ 11 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 11 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,4,12,13,14,15,16,17] := remove (a 9) 11 [0,4,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t5 (t15))

theorem chunk1 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,4,12,13,14,15,16,17])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,1,2])
    (d18 : a 18 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 9 ∈ [0,4] ∧ a 3 ∈ [0,2] ∧ a 2 ∈ [0] ∧ a 18 ∈ [0,2] ∧ a 7 ∈ [0,2] ∧ a 11 ∈ [0,2,6,7,8,9,10,11] := by
  have b0 : a 9 ≠ 12 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 12 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,4,13,14,15,16,17] := remove (a 9) 12 [0,4,12,13,14,15,16,17] d9 b0
  have b1 : a 9 ≠ 13 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 13 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,4,14,15,16,17] := remove (a 9) 13 [0,4,13,14,15,16,17] t0 b1
  have b2 : a 9 ≠ 14 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 14 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,4,15,16,17] := remove (a 9) 14 [0,4,14,15,16,17] t1 b2
  have b3 : a 9 ≠ 15 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 15 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,4,16,17] := remove (a 9) 15 [0,4,15,16,17] t2 b3
  have b4 : a 9 ≠ 16 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 16 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,4,17] := remove (a 9) 16 [0,4,16,17] t3 b4
  have b5 : a 9 ≠ 17 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 17 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,4] := remove (a 9) 17 [0,4,17] t4 b5
  have b6 : a 3 ≠ 1 := exclude [0,1,2] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t6 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b6
  have b7 : a 2 ≠ 1 := exclude [0,1,2,3] (edge r12) (a 2) (a 18) 1 d18 c12 (by decide +kernel)
  have t7 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b7
  have b8 : a 2 ≠ 2 := exclude [0,1,2,3] (edge r12) (a 2) (a 18) 2 d18 c12 (by decide +kernel)
  have t8 : a 2 ∈ [0] := remove (a 2) 2 [0,2] t7 b8
  have b9 : a 18 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 1 t8 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b9
  have b10 : a 18 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 3 t8 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] t9 b10
  have b11 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 1 t6 c13 (by decide +kernel)
  have t11 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b11
  have b12 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 1 t6 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b12
  have b13 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 3 t6 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 11) 3 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 11 ≠ 4 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 4 t6 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 11) 4 [0,2,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 5 t6 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,6,7,8,9,10,11] := remove (a 11) 5 [0,2,5,6,7,8,9,10,11] t14 b15
  exact And.intro t5 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t11 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,6,7,8,9,10,11])
    (d3 : a 3 ∈ [0,2])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,3])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 11 ∈ [0,2,6,8] ∧ a 4 ∈ [0,3] ∧ a 12 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,6,8,9,10,11] := remove (a 11) 7 [0,2,6,7,8,9,10,11] d11 b0
  have b1 : a 11 ≠ 9 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,2,6,8,10,11] := remove (a 11) 9 [0,2,6,8,9,10,11] t0 b1
  have b2 : a 11 ≠ 10 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,6,8,11] := remove (a 11) 10 [0,2,6,8,10,11] t1 b2
  have b3 : a 11 ≠ 11 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,2,6,8] := remove (a 11) 11 [0,2,6,8,11] t2 b3
  have b4 : a 4 ≠ 1 := exclude [0,3] (edge r16) (a 4) (a 5) 1 d5 c16 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b4
  have b5 : a 4 ≠ 2 := exclude [0,3] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0,3,4,5] := remove (a 4) 2 [0,2,3,4,5] t4 b5
  have b6 : a 4 ≠ 4 := exclude [0,3] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t6 : a 4 ∈ [0,3,5] := remove (a 4) 4 [0,3,4,5] t5 b6
  have b7 : a 4 ≠ 5 := exclude [0,3] (edge r16) (a 4) (a 5) 5 d5 c16 (by decide +kernel)
  have t7 : a 4 ∈ [0,3] := remove (a 4) 5 [0,3,5] t6 b7
  have b8 : a 12 ≠ 2 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 2 t7 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b8
  have b9 : a 12 ≠ 3 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 3 t7 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 12 ≠ 4 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 4 t7 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 12 ≠ 5 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 5 t7 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 12 ≠ 6 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 6 t7 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 12 ≠ 7 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 7 t7 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 12 ≠ 8 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 8 t7 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 12 ≠ 9 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 9 t7 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (And.intro t7 (t15))

theorem chunk3 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d4 : a 4 ∈ [0,3])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,3])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d7 : a 7 ∈ [0,2])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 12 ∈ [0,1,10,11] ∧ a 13 ∈ [0,1,2,3,4,5,6,9,10,11] ∧ a 15 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 12 ≠ 12 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 12 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,10,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 12 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b0
  have b1 : a 12 ≠ 13 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 13 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,10,11,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 13 [0,1,10,11,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 12 ≠ 14 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 14 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,10,11,15,16,17,18,19,20,21,22,23] := remove (a 12) 14 [0,1,10,11,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 12 ≠ 15 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 15 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,10,11,16,17,18,19,20,21,22,23] := remove (a 12) 15 [0,1,10,11,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 12 ≠ 16 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 16 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,10,11,17,18,19,20,21,22,23] := remove (a 12) 16 [0,1,10,11,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 12 ≠ 17 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 17 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,10,11,18,19,20,21,22,23] := remove (a 12) 17 [0,1,10,11,17,18,19,20,21,22,23] t4 b5
  have b6 : a 12 ≠ 18 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 18 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,10,11,19,20,21,22,23] := remove (a 12) 18 [0,1,10,11,18,19,20,21,22,23] t5 b6
  have b7 : a 12 ≠ 19 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 19 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,10,11,20,21,22,23] := remove (a 12) 19 [0,1,10,11,19,20,21,22,23] t6 b7
  have b8 : a 12 ≠ 20 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 20 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,10,11,21,22,23] := remove (a 12) 20 [0,1,10,11,20,21,22,23] t7 b8
  have b9 : a 12 ≠ 21 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 21 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,10,11,22,23] := remove (a 12) 21 [0,1,10,11,21,22,23] t8 b9
  have b10 : a 12 ≠ 22 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 22 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,10,11,23] := remove (a 12) 22 [0,1,10,11,22,23] t9 b10
  have b11 : a 12 ≠ 23 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 23 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,10,11] := remove (a 12) 23 [0,1,10,11,23] t10 b11
  have b12 : a 13 ≠ 7 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,3,4,5,6,8,9,10,11] := remove (a 13) 7 [0,1,2,3,4,5,6,7,8,9,10,11] d13 b12
  have b13 : a 13 ≠ 8 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,3,4,5,6,9,10,11] := remove (a 13) 8 [0,1,2,3,4,5,6,8,9,10,11] t12 b13
  have b14 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d15 b14
  have b15 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t11 (And.intro t13 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_175
