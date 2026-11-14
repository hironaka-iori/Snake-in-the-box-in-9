import PartitionData205_210
namespace PartitionCover205_210
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d1 : a 1 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    : a 2 ∈ [0,6] ∧ a 4 ∈ [0,2,6,8] ∧ a 17 ∈ [0,1,2,3,5] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 2) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 2) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 2) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,5,6,7,8,9,10,11] := remove (a 2) 4 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0,6,7,8,9,10,11] := remove (a 2) 5 [0,5,6,7,8,9,10,11] t3 b4
  have b5 : a 2 ≠ 7 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 7 d0 c1 (by decide +kernel)
  have t5 : a 2 ∈ [0,6,8,9,10,11] := remove (a 2) 7 [0,6,7,8,9,10,11] t4 b5
  have b6 : a 2 ≠ 8 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 8 d0 c1 (by decide +kernel)
  have t6 : a 2 ∈ [0,6,9,10,11] := remove (a 2) 8 [0,6,8,9,10,11] t5 b6
  have b7 : a 2 ≠ 9 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 9 d0 c1 (by decide +kernel)
  have t7 : a 2 ∈ [0,6,10,11] := remove (a 2) 9 [0,6,9,10,11] t6 b7
  have b8 : a 2 ≠ 10 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 10 d0 c1 (by decide +kernel)
  have t8 : a 2 ∈ [0,6,11] := remove (a 2) 10 [0,6,10,11] t7 b8
  have b9 : a 2 ≠ 11 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 11 d0 c1 (by decide +kernel)
  have t9 : a 2 ∈ [0,6] := remove (a 2) 11 [0,6,11] t8 b9
  have b10 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,2,3,4,5,6,7,8] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8] d4 b10
  have b11 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,2,4,5,6,7,8] := remove (a 4) 3 [0,2,3,4,5,6,7,8] t10 b11
  have b12 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t12 : a 4 ∈ [0,2,5,6,7,8] := remove (a 4) 4 [0,2,4,5,6,7,8] t11 b12
  have b13 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t13 : a 4 ∈ [0,2,6,7,8] := remove (a 4) 5 [0,2,5,6,7,8] t12 b13
  have b14 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t14 : a 4 ∈ [0,2,6,8] := remove (a 4) 7 [0,2,6,7,8] t13 b14
  have b15 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t15 : a 17 ∈ [0,1,2,3,5] := remove (a 17) 4 [0,1,2,3,4,5] d17 b15
  exact And.intro t9 (And.intro t14 (t15))

theorem chunk1 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,2,3,5])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0,1,2,3,4,5])
    (d2 : a 2 ∈ [0,6])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 17 ∈ [0,1,2,3] ∧ a 3 ∈ [0,3] ∧ a 18 ∈ [0,1,6,7,10,11,12,13] ∧ a 19 ∈ [0,2,3,4,5,6,7,8] := by
  have b0 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t0 : a 17 ∈ [0,1,2,3] := remove (a 17) 5 [0,1,2,3,5] d17 b0
  have b1 : a 3 ≠ 1 := exclude [0,6] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t1 : a 3 ∈ [0,2,3,4,5] := remove (a 3) 1 [0,1,2,3,4,5] d3 b1
  have b2 : a 3 ≠ 2 := exclude [0,6] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t2 : a 3 ∈ [0,3,4,5] := remove (a 3) 2 [0,2,3,4,5] t1 b2
  have b3 : a 3 ≠ 4 := exclude [0,6] (fun u v => edge r9 v u) (a 3) (a 2) 4 d2 c9 (by decide +kernel)
  have t3 : a 3 ∈ [0,3,5] := remove (a 3) 4 [0,3,4,5] t2 b3
  have b4 : a 3 ≠ 5 := exclude [0,6] (fun u v => edge r9 v u) (a 3) (a 2) 5 d2 c9 (by decide +kernel)
  have t4 : a 3 ∈ [0,3] := remove (a 3) 5 [0,3,5] t3 b4
  have b5 : a 18 ≠ 2 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d18 b5
  have b6 : a 18 ≠ 3 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 18 ≠ 4 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 18 ≠ 5 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 18 ≠ 8 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 18) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 18 ≠ 9 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 18) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 18 ≠ 14 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 14 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,1,6,7,10,11,12,13,15,16,17] := remove (a 18) 14 [0,1,6,7,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 18 ≠ 15 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 15 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,6,7,10,11,12,13,16,17] := remove (a 18) 15 [0,1,6,7,10,11,12,13,15,16,17] t11 b12
  have b13 : a 18 ≠ 16 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,6,7,10,11,12,13,17] := remove (a 18) 16 [0,1,6,7,10,11,12,13,16,17] t12 b13
  have b14 : a 18 ≠ 17 := exclude [0,6] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,6,7,10,11,12,13] := remove (a 18) 17 [0,1,6,7,10,11,12,13,17] t13 b14
  have b15 : a 19 ≠ 1 := exclude [0,3] (fun u v => edge r15 v u) (a 19) (a 3) 1 t4 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,2,3,4,5,6,7,8] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8] d19 b15
  exact And.intro t0 (And.intro t4 (And.intro t14 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,2,3,4,5,6,7,8])
    (d3 : a 3 ∈ [0,3])
    (d5 : a 5 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,2,6,8])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 19 ∈ [0,3,5,6] ∧ a 5 ∈ [0,2] ∧ a 6 ∈ [0,1,4,5] ∧ a 12 ∈ [0,1,4,5,12,13,14,15,16,17] := by
  have b0 : a 19 ≠ 2 := exclude [0,3] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,3,4,5,6,7,8] := remove (a 19) 2 [0,2,3,4,5,6,7,8] d19 b0
  have b1 : a 19 ≠ 4 := exclude [0,3] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,3,5,6,7,8] := remove (a 19) 4 [0,3,4,5,6,7,8] t0 b1
  have b2 : a 19 ≠ 7 := exclude [0,3] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,3,5,6,8] := remove (a 19) 7 [0,3,5,6,7,8] t1 b2
  have b3 : a 19 ≠ 8 := exclude [0,3] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,3,5,6] := remove (a 19) 8 [0,3,5,6,8] t2 b3
  have b4 : a 5 ≠ 1 := exclude [0,2,6,8] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t4 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b4
  have b5 : a 5 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t5 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t4 b5
  have b6 : a 6 ≠ 2 := exclude [0,2,6,8] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t6 : a 6 ∈ [0,1,3,4,5] := remove (a 6) 2 [0,1,2,3,4,5] d6 b6
  have b7 : a 6 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r17 v u) (a 6) (a 4) 3 d4 c17 (by decide +kernel)
  have t7 : a 6 ∈ [0,1,4,5] := remove (a 6) 3 [0,1,3,4,5] t6 b7
  have b8 : a 12 ≠ 2 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d12 b8
  have b9 : a 12 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 12 ≠ 6 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 12 ≠ 7 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 12 ≠ 8 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17] := remove (a 12) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 12 ≠ 9 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,4,5,10,11,12,13,14,15,16,17] := remove (a 12) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 12 ≠ 10 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 10 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,4,5,11,12,13,14,15,16,17] := remove (a 12) 10 [0,1,4,5,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 12 ≠ 11 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 11 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,4,5,12,13,14,15,16,17] := remove (a 12) 11 [0,1,4,5,11,12,13,14,15,16,17] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t7 (t15)))

theorem chunk3 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,4,5,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,2,6,8])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7])
    (d7 : a 7 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d21 : a 21 ∈ [0,1,2,3])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 12 ∈ [0,1,4,5,12,13,16,17] ∧ a 20 ∈ [0,4] ∧ a 7 ∈ [0,2] ∧ a 13 ∈ [0,1,2] ∧ a 21 ∈ [0,2,3] := by
  have b0 : a 12 ≠ 14 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 14 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,4,5,12,13,15,16,17] := remove (a 12) 14 [0,1,4,5,12,13,14,15,16,17] d12 b0
  have b1 : a 12 ≠ 15 := exclude [0,2,6,8] (fun u v => edge r18 v u) (a 12) (a 4) 15 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,4,5,12,13,16,17] := remove (a 12) 15 [0,1,4,5,12,13,15,16,17] t0 b1
  have b2 : a 20 ≠ 1 := exclude [0,2,6,8] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,2,3,4,5,6,7] := remove (a 20) 1 [0,1,2,3,4,5,6,7] d20 b2
  have b3 : a 20 ≠ 2 := exclude [0,2,6,8] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,3,4,5,6,7] := remove (a 20) 2 [0,2,3,4,5,6,7] t2 b3
  have b4 : a 20 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,4,5,6,7] := remove (a 20) 3 [0,3,4,5,6,7] t3 b4
  have b5 : a 20 ≠ 5 := exclude [0,2,6,8] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,4,6,7] := remove (a 20) 5 [0,4,5,6,7] t4 b5
  have b6 : a 20 ≠ 6 := exclude [0,2,6,8] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,4,7] := remove (a 20) 6 [0,4,6,7] t5 b6
  have b7 : a 20 ≠ 7 := exclude [0,2,6,8] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,4] := remove (a 20) 7 [0,4,7] t6 b7
  have b8 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t8 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b8
  have b9 : a 13 ≠ 3 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,2,4,5,6,7,8] := remove (a 13) 3 [0,1,2,3,4,5,6,7,8] d13 b9
  have b10 : a 13 ≠ 4 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,2,5,6,7,8] := remove (a 13) 4 [0,1,2,4,5,6,7,8] t9 b10
  have b11 : a 13 ≠ 5 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,2,6,7,8] := remove (a 13) 5 [0,1,2,5,6,7,8] t10 b11
  have b12 : a 13 ≠ 6 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,7,8] := remove (a 13) 6 [0,1,2,6,7,8] t11 b12
  have b13 : a 13 ≠ 7 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,8] := remove (a 13) 7 [0,1,2,7,8] t12 b13
  have b14 : a 13 ≠ 8 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,2] := remove (a 13) 8 [0,1,2,8] t13 b14
  have b15 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t15 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b15
  exact And.intro t1 (And.intro t7 (And.intro t8 (And.intro t14 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_210
