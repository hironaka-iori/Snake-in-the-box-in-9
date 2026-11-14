import PartitionData205_194
namespace PartitionCover205_194
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (d1 : a 1 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7])
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 8 ∈ [0,1] ∧ a 16 ∈ [0,2] ∧ a 5 ∈ [0,2,3,4,6,7] ∧ a 9 ∈ [0,2,3,4,6,7] ∧ a 17 ∈ [0,2,3,4,6,7] ∧ a 2 ∈ [0,1,2,4] ∧ a 6 ∈ [0,1,2,4] := by
  have b0 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,3,4,5] := remove (a 8) 2 [0,1,2,3,4,5] d8 b0
  have b1 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,4,5] := remove (a 8) 3 [0,1,3,4,5] t0 b1
  have b2 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,5] := remove (a 8) 4 [0,1,4,5] t1 b2
  have b3 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1] := remove (a 8) 5 [0,1,5] t2 b3
  have b4 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b4
  have b5 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t4 b5
  have b6 : a 5 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,3,4,5,6,7] := remove (a 5) 1 [0,1,2,3,4,5,6,7] d5 b6
  have b7 : a 5 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,2,3,4,6,7] := remove (a 5) 5 [0,2,3,4,5,6,7] t6 b7
  have b8 : a 9 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t8 : a 9 ∈ [0,2,3,4,5,6,7] := remove (a 9) 1 [0,1,2,3,4,5,6,7] d9 b8
  have b9 : a 9 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t9 : a 9 ∈ [0,2,3,4,6,7] := remove (a 9) 5 [0,2,3,4,5,6,7] t8 b9
  have b10 : a 17 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,2,3,4,5,6,7] := remove (a 17) 1 [0,1,2,3,4,5,6,7] d17 b10
  have b11 : a 17 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t11 : a 17 ∈ [0,2,3,4,6,7] := remove (a 17) 5 [0,2,3,4,5,6,7] t10 b11
  have b12 : a 2 ≠ 3 := exclude [0,1,2,3] (edge r9) (a 2) (a 3) 3 d3 c9 (by decide +kernel)
  have t12 : a 2 ∈ [0,1,2,4,5] := remove (a 2) 3 [0,1,2,3,4,5] d2 b12
  have b13 : a 2 ≠ 5 := exclude [0,1,2,3] (edge r9) (a 2) (a 3) 5 d3 c9 (by decide +kernel)
  have t13 : a 2 ∈ [0,1,2,4] := remove (a 2) 5 [0,1,2,4,5] t12 b13
  have b14 : a 6 ≠ 3 := exclude [0,1,2,4] (fun u v => edge r10 v u) (a 6) (a 2) 3 t13 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,2,4,5] := remove (a 6) 3 [0,1,2,3,4,5] d6 b14
  have b15 : a 6 ≠ 5 := exclude [0,1,2,4] (fun u v => edge r10 v u) (a 6) (a 2) 5 t13 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,2,4] := remove (a 6) 5 [0,1,2,4,5] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t13 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,1,2,4])
    (d3 : a 3 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1,2])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 18 ∈ [0,1,2,4,5,6,7,9,10] ∧ a 3 ∈ [0,1] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0,3,11] := by
  have b0 : a 18 ≠ 3 := exclude [0,1,2,4] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 18) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b0
  have b1 : a 18 ≠ 8 := exclude [0,1,2,4] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,2,4,5,6,7,9,10,11] := remove (a 18) 8 [0,1,2,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 18 ≠ 11 := exclude [0,1,2,4] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,2,4,5,6,7,9,10] := remove (a 18) 11 [0,1,2,4,5,6,7,9,10,11] t1 b2
  have b3 : a 3 ≠ 2 := exclude [0,1,2] (edge r14) (a 3) (a 11) 2 d11 c14 (by decide +kernel)
  have t3 : a 3 ∈ [0,1,3] := remove (a 3) 2 [0,1,2,3] d3 b3
  have b4 : a 3 ≠ 3 := exclude [0,1,2] (edge r14) (a 3) (a 11) 3 d11 c14 (by decide +kernel)
  have t4 : a 3 ∈ [0,1] := remove (a 3) 3 [0,1,3] t3 b4
  have b5 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 t4 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,2] := remove (a 11) 1 [0,1,2] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 t4 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0] := remove (a 11) 2 [0,2] t5 b6
  have b7 : a 19 ≠ 1 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 1 t4 c15 (by decide +kernel)
  have t7 : a 19 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b7
  have b8 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 2 t4 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 19 ≠ 4 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 4 t4 c15 (by decide +kernel)
  have t9 : a 19 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 19) 4 [0,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 t4 c15 (by decide +kernel)
  have t10 : a 19 ∈ [0,3,6,7,8,9,10,11] := remove (a 19) 5 [0,3,5,6,7,8,9,10,11] t9 b10
  have b11 : a 19 ≠ 6 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 6 t4 c15 (by decide +kernel)
  have t11 : a 19 ∈ [0,3,7,8,9,10,11] := remove (a 19) 6 [0,3,6,7,8,9,10,11] t10 b11
  have b12 : a 19 ≠ 7 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 7 t4 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,3,8,9,10,11] := remove (a 19) 7 [0,3,7,8,9,10,11] t11 b12
  have b13 : a 19 ≠ 8 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 8 t4 c15 (by decide +kernel)
  have t13 : a 19 ∈ [0,3,9,10,11] := remove (a 19) 8 [0,3,8,9,10,11] t12 b13
  have b14 : a 19 ≠ 9 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 9 t4 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,3,10,11] := remove (a 19) 9 [0,3,9,10,11] t13 b14
  have b15 : a 19 ≠ 10 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 10 t4 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,3,11] := remove (a 19) 10 [0,3,10,11] t14 b15
  exact And.intro t2 (And.intro t4 (And.intro t6 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,3,11])
    (d3 : a 3 ∈ [0,1])
    (d5 : a 5 ∈ [0,2,3,4,6,7])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,4])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 19 ∈ [0,3] ∧ a 5 ∈ [0,2,4,6] ∧ a 6 ∈ [0,1] ∧ a 13 ∈ [0,2,4,6] ∧ a 21 ∈ [0,2,4,6] ∧ a 14 ∈ [0,1,3,5] ∧ a 22 ∈ [0,1,2,3,4,5,7,8] := by
  have b0 : a 19 ≠ 11 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 11 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,3] := remove (a 19) 11 [0,3,11] d19 b0
  have b1 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t1 : a 5 ∈ [0,2,4,6,7] := remove (a 5) 3 [0,2,3,4,6,7] d5 b1
  have b2 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 7 d4 c16 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,4,6] := remove (a 5) 7 [0,2,4,6,7] t1 b2
  have b3 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,4] := remove (a 6) 2 [0,1,2,4] d6 b3
  have b4 : a 6 ≠ 4 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 4 d4 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0,1] := remove (a 6) 4 [0,1,4] t3 b4
  have b5 : a 13 ≠ 1 := exclude [0,2,4,6] (fun u v => edge r21 v u) (a 13) (a 5) 1 t2 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,2,3,4,5,6,7] := remove (a 13) 1 [0,1,2,3,4,5,6,7] d13 b5
  have b6 : a 13 ≠ 3 := exclude [0,2,4,6] (fun u v => edge r21 v u) (a 13) (a 5) 3 t2 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,2,4,5,6,7] := remove (a 13) 3 [0,2,3,4,5,6,7] t5 b6
  have b7 : a 13 ≠ 5 := exclude [0,2,4,6] (fun u v => edge r21 v u) (a 13) (a 5) 5 t2 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,2,4,6,7] := remove (a 13) 5 [0,2,4,5,6,7] t6 b7
  have b8 : a 13 ≠ 7 := exclude [0,2,4,6] (fun u v => edge r21 v u) (a 13) (a 5) 7 t2 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,4,6] := remove (a 13) 7 [0,2,4,6,7] t7 b8
  have b9 : a 21 ≠ 1 := exclude [0,2,4,6] (fun u v => edge r22 v u) (a 21) (a 5) 1 t2 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,2,3,4,5,6,7] := remove (a 21) 1 [0,1,2,3,4,5,6,7] d21 b9
  have b10 : a 21 ≠ 3 := exclude [0,2,4,6] (fun u v => edge r22 v u) (a 21) (a 5) 3 t2 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,2,4,5,6,7] := remove (a 21) 3 [0,2,3,4,5,6,7] t9 b10
  have b11 : a 21 ≠ 5 := exclude [0,2,4,6] (fun u v => edge r22 v u) (a 21) (a 5) 5 t2 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,4,6,7] := remove (a 21) 5 [0,2,4,5,6,7] t10 b11
  have b12 : a 21 ≠ 7 := exclude [0,2,4,6] (fun u v => edge r22 v u) (a 21) (a 5) 7 t2 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,2,4,6] := remove (a 21) 7 [0,2,4,6,7] t11 b12
  have b13 : a 14 ≠ 2 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 2 t4 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,3,4,5] := remove (a 14) 2 [0,1,2,3,4,5] d14 b13
  have b14 : a 14 ≠ 4 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 4 t4 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,3,5] := remove (a 14) 4 [0,1,3,4,5] t13 b14
  have b15 : a 22 ≠ 6 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 6 t4 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,2,3,4,5,7,8] := remove (a 22) 6 [0,1,2,3,4,5,6,7,8] d22 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t8 (And.intro t12 (And.intro t14 (t15))))))

theorem chunk3 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,3,4,5,7,8])
    (d6 : a 6 ∈ [0,1])
    (d9 : a 9 ∈ [0,2,3,4,6,7])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 22 ∈ [0,1,2,3,4,5] ∧ a 9 ∈ [0,4] ∧ a 10 ∈ [0,1] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0,2,6,7,8,9,10,11] := by
  have b0 : a 22 ≠ 7 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,2,3,4,5,8] := remove (a 22) 7 [0,1,2,3,4,5,7,8] d22 b0
  have b1 : a 22 ≠ 8 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,1,2,3,4,5] := remove (a 22) 8 [0,1,2,3,4,5,8] t0 b1
  have b2 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 2 d8 c28 (by decide +kernel)
  have t2 : a 9 ∈ [0,3,4,6,7] := remove (a 9) 2 [0,2,3,4,6,7] d9 b2
  have b3 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 3 d8 c28 (by decide +kernel)
  have t3 : a 9 ∈ [0,4,6,7] := remove (a 9) 3 [0,3,4,6,7] t2 b3
  have b4 : a 9 ≠ 6 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 6 d8 c28 (by decide +kernel)
  have t4 : a 9 ∈ [0,4,7] := remove (a 9) 6 [0,4,6,7] t3 b4
  have b5 : a 9 ≠ 7 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 7 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0,4] := remove (a 9) 7 [0,4,7] t4 b5
  have b6 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,3,4,5] := remove (a 10) 2 [0,1,2,3,4,5] d10 b6
  have b7 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,4,5] := remove (a 10) 3 [0,1,3,4,5] t6 b7
  have b8 : a 10 ≠ 4 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 4 d8 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,5] := remove (a 10) 4 [0,1,4,5] t7 b8
  have b9 : a 10 ≠ 5 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 5 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,1] := remove (a 10) 5 [0,1,5] t8 b9
  have b10 : a 12 ≠ 1 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 1 d8 c30 (by decide +kernel)
  have t10 : a 12 ∈ [0,2] := remove (a 12) 1 [0,1,2] d12 b10
  have b11 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 2 d8 c30 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 2 [0,2] t10 b11
  have b12 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b12
  have b13 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 24) 4 [0,2,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,2,6,7,8,9,10,11] := remove (a 24) 5 [0,2,5,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t9 (And.intro t11 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_194
