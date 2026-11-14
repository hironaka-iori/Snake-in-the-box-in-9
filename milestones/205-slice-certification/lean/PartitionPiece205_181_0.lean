import PartitionData205_181
namespace PartitionCover205_181
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,1,2])
    (d18 : a 18 ∈ [0,1])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 4 ∈ [0,1] ∧ a 8 ∈ [0,6] ∧ a 2 ∈ [0] := by
  have b0 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,3,4,5] := remove (a 4) 2 [0,1,2,3,4,5] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,4,5] := remove (a 4) 3 [0,1,3,4,5] t0 b1
  have b2 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,5] := remove (a 4) 4 [0,1,4,5] t1 b2
  have b3 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,1] := remove (a 4) 5 [0,1,5] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d8 b4
  have b5 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 8) 2 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 8) 3 [0,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,5,6,7,8,9,10,11] := remove (a 8) 4 [0,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,6,7,8,9,10,11] := remove (a 8) 5 [0,5,6,7,8,9,10,11] t7 b8
  have b9 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,6,8,9,10,11] := remove (a 8) 7 [0,6,7,8,9,10,11] t8 b9
  have b10 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,6,9,10,11] := remove (a 8) 8 [0,6,8,9,10,11] t9 b10
  have b11 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,6,10,11] := remove (a 8) 9 [0,6,9,10,11] t10 b11
  have b12 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,6,11] := remove (a 8) 10 [0,6,10,11] t11 b12
  have b13 : a 8 ≠ 11 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 11 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,6] := remove (a 8) 11 [0,6,11] t12 b13
  have b14 : a 2 ≠ 1 := exclude [0,1] (edge r12) (a 2) (a 18) 1 d18 c12 (by decide +kernel)
  have t14 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b14
  have b15 : a 2 ≠ 2 := exclude [0,1] (edge r12) (a 2) (a 18) 2 d18 c12 (by decide +kernel)
  have t15 : a 2 ∈ [0] := remove (a 2) 2 [0,2] t14 b15
  exact And.intro t3 (And.intro t13 (t15))

theorem chunk1 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8])
    (d4 : a 4 ∈ [0,1])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    : a 7 ∈ [0,3] ∧ a 11 ∈ [0,1,6,7] ∧ a 5 ∈ [0,1,2,3,8] := by
  have b0 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 1 d3 c13 (by decide +kernel)
  have t0 : a 7 ∈ [0,2,3,4,5] := remove (a 7) 1 [0,1,2,3,4,5] d7 b0
  have b1 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t1 : a 7 ∈ [0,3,4,5] := remove (a 7) 2 [0,2,3,4,5] t0 b1
  have b2 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 4 d3 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0,3,5] := remove (a 7) 4 [0,3,4,5] t1 b2
  have b3 : a 7 ≠ 5 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 5 d3 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0,3] := remove (a 7) 5 [0,3,5] t2 b3
  have b4 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 11) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b4
  have b5 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 11) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 11) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,1,6,7,8,9,10,11] := remove (a 11) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,6,7,9,10,11] := remove (a 11) 8 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,6,7,10,11] := remove (a 11) 9 [0,1,6,7,9,10,11] t8 b9
  have b10 : a 11 ≠ 10 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,1,6,7,11] := remove (a 11) 10 [0,1,6,7,10,11] t9 b10
  have b11 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,1,6,7] := remove (a 11) 11 [0,1,6,7,11] t10 b11
  have b12 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,2,3,5,6,7,8] := remove (a 5) 4 [0,1,2,3,4,5,6,7,8] d5 b12
  have b13 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 5 d4 c16 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,2,3,6,7,8] := remove (a 5) 5 [0,1,2,3,5,6,7,8] t12 b13
  have b14 : a 5 ≠ 6 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 6 d4 c16 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,2,3,7,8] := remove (a 5) 6 [0,1,2,3,6,7,8] t13 b14
  have b15 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 7 d4 c16 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,2,3,8] := remove (a 5) 7 [0,1,2,3,7,8] t14 b15
  exact And.intro t3 (And.intro t11 (t15))

theorem chunk2 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,2,3,8])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 5 ∈ [0,1,2,3] ∧ a 6 ∈ [0,1] ∧ a 12 ∈ [0,1,2,3] ∧ a 20 ∈ [0,1,2,3,7,8,9,10,11] := by
  have b0 : a 5 ≠ 8 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 8 d4 c16 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,2,3] := remove (a 5) 8 [0,1,2,3,8] d5 b0
  have b1 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,3,4,5] := remove (a 6) 2 [0,1,2,3,4,5] d6 b1
  have b2 : a 6 ≠ 3 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 3 d4 c17 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,4,5] := remove (a 6) 3 [0,1,3,4,5] t1 b2
  have b3 : a 6 ≠ 4 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 4 d4 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,5] := remove (a 6) 4 [0,1,4,5] t2 b3
  have b4 : a 6 ≠ 5 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 5 d4 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0,1] := remove (a 6) 5 [0,1,5] t3 b4
  have b5 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 12) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b5
  have b6 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 12) 5 [0,1,2,3,5,6,7,8,9,10,11] t5 b6
  have b7 : a 12 ≠ 6 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 12) 6 [0,1,2,3,6,7,8,9,10,11] t6 b7
  have b8 : a 12 ≠ 7 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,2,3,8,9,10,11] := remove (a 12) 7 [0,1,2,3,7,8,9,10,11] t7 b8
  have b9 : a 12 ≠ 8 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,2,3,9,10,11] := remove (a 12) 8 [0,1,2,3,8,9,10,11] t8 b9
  have b10 : a 12 ≠ 9 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,2,3,10,11] := remove (a 12) 9 [0,1,2,3,9,10,11] t9 b10
  have b11 : a 12 ≠ 10 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 10 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,2,3,11] := remove (a 12) 10 [0,1,2,3,10,11] t10 b11
  have b12 : a 12 ≠ 11 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 11 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,2,3] := remove (a 12) 11 [0,1,2,3,11] t11 b12
  have b13 : a 20 ≠ 4 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 20) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b13
  have b14 : a 20 ≠ 5 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 20) 5 [0,1,2,3,5,6,7,8,9,10,11] t13 b14
  have b15 : a 20 ≠ 6 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 20) 6 [0,1,2,3,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t12 (t15)))

theorem chunk3 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,2,3,7,8,9,10,11])
    (d4 : a 4 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d6 : a 6 ∈ [0,1])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 20 ∈ [0,1,2,3] ∧ a 13 ∈ [0,1,3,5] ∧ a 21 ∈ [0,1,3,5] ∧ a 14 ∈ [0,4,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 20 ≠ 7 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,2,3,8,9,10,11] := remove (a 20) 7 [0,1,2,3,7,8,9,10,11] d20 b0
  have b1 : a 20 ≠ 8 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,2,3,9,10,11] := remove (a 20) 8 [0,1,2,3,8,9,10,11] t0 b1
  have b2 : a 20 ≠ 9 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,2,3,10,11] := remove (a 20) 9 [0,1,2,3,9,10,11] t1 b2
  have b3 : a 20 ≠ 10 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,2,3,11] := remove (a 20) 10 [0,1,2,3,10,11] t2 b3
  have b4 : a 20 ≠ 11 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,2,3] := remove (a 20) 11 [0,1,2,3,11] t3 b4
  have b5 : a 13 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b5
  have b6 : a 13 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,3,5] := remove (a 13) 4 [0,1,3,4,5] t5 b6
  have b7 : a 21 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b7
  have b8 : a 21 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,3,5] := remove (a 21) 4 [0,1,3,4,5] t7 b8
  have b9 : a 14 ≠ 1 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b9
  have b10 : a 14 ≠ 2 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 14 ≠ 3 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 14 ≠ 5 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 14 ≠ 6 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 14 ≠ 7 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,4,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 14 ≠ 8 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,4,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,4,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t4 (And.intro t6 (And.intro t8 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_181
