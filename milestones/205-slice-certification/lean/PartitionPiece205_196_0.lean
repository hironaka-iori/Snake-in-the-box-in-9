import PartitionData205_196
namespace PartitionCover205_196
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8])
    (d3 : a 3 ∈ [0,1,2])
    (d1 : a 1 ∈ [0,1])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    : a 4 ∈ [0,1,3,5] ∧ a 8 ∈ [0,1,2,3] ∧ a 16 ∈ [0,3] ∧ a 3 ∈ [0,2] ∧ a 5 ∈ [0,3,6,7,8] := by
  have b0 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,3,4,5] := remove (a 4) 2 [0,1,2,3,4,5] d4 b0
  have b1 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,3,5] := remove (a 4) 4 [0,1,3,4,5] t0 b1
  have b2 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,2,3,5] := remove (a 8) 4 [0,1,2,3,4,5] d8 b2
  have b3 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1,2,3] := remove (a 8) 5 [0,1,2,3,5] t2 b3
  have b4 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,2,3,4,5,6,7,8] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8] d16 b4
  have b5 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,3,4,5,6,7,8] := remove (a 16) 2 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,3,5,6,7,8] := remove (a 16) 4 [0,3,4,5,6,7,8] t5 b6
  have b7 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,3,6,7,8] := remove (a 16) 5 [0,3,5,6,7,8] t6 b7
  have b8 : a 16 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 6 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,3,7,8] := remove (a 16) 6 [0,3,6,7,8] t7 b8
  have b9 : a 16 ≠ 7 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 7 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,3,8] := remove (a 16) 7 [0,3,7,8] t8 b9
  have b10 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,3] := remove (a 16) 8 [0,3,8] t9 b10
  have b11 : a 3 ≠ 1 := exclude [0,1] (fun u v => edge r5 v u) (a 3) (a 1) 1 d1 c5 (by decide +kernel)
  have t11 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b11
  have b12 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t12 : a 5 ∈ [0,2,3,4,5,6,7,8] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8] d5 b12
  have b13 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,3,4,5,6,7,8] := remove (a 5) 2 [0,2,3,4,5,6,7,8] t12 b13
  have b14 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,3,5,6,7,8] := remove (a 5) 4 [0,3,4,5,6,7,8] t13 b14
  have b15 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t15 : a 5 ∈ [0,3,6,7,8] := remove (a 5) 5 [0,3,5,6,7,8] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t10 (And.intro t11 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,3,6,7,8])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8])
    (d18 : a 18 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0,1,2])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (d3 : a 3 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 5 ∈ [0,3] ∧ a 9 ∈ [0,2] ∧ a 17 ∈ [0,3] ∧ a 18 ∈ [0,1,3] ∧ a 11 ∈ [0,1,3,4,5,6,7,8] := by
  have b0 : a 5 ≠ 6 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 6 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0,3,7,8] := remove (a 5) 6 [0,3,6,7,8] d5 b0
  have b1 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 7 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0,3,8] := remove (a 5) 7 [0,3,7,8] t0 b1
  have b2 : a 5 ≠ 8 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 8 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,3] := remove (a 5) 8 [0,3,8] t1 b2
  have b3 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b3
  have b4 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,4,5] := remove (a 9) 3 [0,2,3,4,5] t3 b4
  have b5 : a 9 ≠ 4 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,2,5] := remove (a 9) 4 [0,2,4,5] t4 b5
  have b6 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0,2] := remove (a 9) 5 [0,2,5] t5 b6
  have b7 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,2,3,4,5,6,7,8] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8] d17 b7
  have b8 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t8 : a 17 ∈ [0,3,4,5,6,7,8] := remove (a 17) 2 [0,2,3,4,5,6,7,8] t7 b8
  have b9 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t9 : a 17 ∈ [0,3,5,6,7,8] := remove (a 17) 4 [0,3,4,5,6,7,8] t8 b9
  have b10 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 5 d1 c8 (by decide +kernel)
  have t10 : a 17 ∈ [0,3,6,7,8] := remove (a 17) 5 [0,3,5,6,7,8] t9 b10
  have b11 : a 17 ≠ 6 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t11 : a 17 ∈ [0,3,7,8] := remove (a 17) 6 [0,3,6,7,8] t10 b11
  have b12 : a 17 ≠ 7 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t12 : a 17 ∈ [0,3,8] := remove (a 17) 7 [0,3,7,8] t11 b12
  have b13 : a 17 ≠ 8 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t13 : a 17 ∈ [0,3] := remove (a 17) 8 [0,3,8] t12 b13
  have b14 : a 18 ≠ 2 := exclude [0,1,2] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,3] := remove (a 18) 2 [0,1,2,3] d18 b14
  have b15 : a 11 ≠ 2 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,1,3,4,5,6,7,8] := remove (a 11) 2 [0,1,2,3,4,5,6,7,8] d11 b15
  exact And.intro t2 (And.intro t6 (And.intro t13 (And.intro t14 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,3,4,5,6,7,8])
    (d3 : a 3 ∈ [0,2])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,1,3,5])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,3])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    : a 11 ∈ [0,1,4,5,7,8] ∧ a 19 ∈ [0,1,2,3,4,5] ∧ a 6 ∈ [0,1,3,5] ∧ a 12 ∈ [0,2,6,10] ∧ a 7 ∈ [0,1,2,4,5] := by
  have b0 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,1,4,5,6,7,8] := remove (a 11) 3 [0,1,3,4,5,6,7,8] d11 b0
  have b1 : a 11 ≠ 6 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,1,4,5,7,8] := remove (a 11) 6 [0,1,4,5,6,7,8] t0 b1
  have b2 : a 19 ≠ 6 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 6 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,2,3,4,5,7,8] := remove (a 19) 6 [0,1,2,3,4,5,6,7,8] d19 b2
  have b3 : a 19 ≠ 7 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,2,3,4,5,8] := remove (a 19) 7 [0,1,2,3,4,5,7,8] t2 b3
  have b4 : a 19 ≠ 8 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,2,3,4,5] := remove (a 19) 8 [0,1,2,3,4,5,8] t3 b4
  have b5 : a 6 ≠ 2 := exclude [0,1,3,5] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t5 : a 6 ∈ [0,1,3,4,5] := remove (a 6) 2 [0,1,2,3,4,5] d6 b5
  have b6 : a 6 ≠ 4 := exclude [0,1,3,5] (fun u v => edge r17 v u) (a 6) (a 4) 4 d4 c17 (by decide +kernel)
  have t6 : a 6 ∈ [0,1,3,5] := remove (a 6) 4 [0,1,3,4,5] t5 b6
  have b7 : a 12 ≠ 1 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b7
  have b8 : a 12 ≠ 3 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 12) 3 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 12 ≠ 4 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 12) 4 [0,2,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 12 ≠ 5 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,2,6,7,8,9,10,11] := remove (a 12) 5 [0,2,5,6,7,8,9,10,11] t9 b10
  have b11 : a 12 ≠ 7 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,6,8,9,10,11] := remove (a 12) 7 [0,2,6,7,8,9,10,11] t10 b11
  have b12 : a 12 ≠ 8 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,2,6,9,10,11] := remove (a 12) 8 [0,2,6,8,9,10,11] t11 b12
  have b13 : a 12 ≠ 9 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,2,6,10,11] := remove (a 12) 9 [0,2,6,9,10,11] t12 b13
  have b14 : a 12 ≠ 11 := exclude [0,1,3,5] (fun u v => edge r18 v u) (a 12) (a 4) 11 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,6,10] := remove (a 12) 11 [0,2,6,10,11] t13 b14
  have b15 : a 7 ≠ 3 := exclude [0,3] (fun u v => edge r20 v u) (a 7) (a 5) 3 d5 c20 (by decide +kernel)
  have t15 : a 7 ∈ [0,1,2,4,5] := remove (a 7) 3 [0,1,2,3,4,5] d7 b15
  exact And.intro t1 (And.intro t4 (And.intro t6 (And.intro t14 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2,4,5])
    (d5 : a 5 ∈ [0,3])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1,3,5])
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 7 ∈ [0,1,2,4] ∧ a 13 ∈ [0,2] ∧ a 21 ∈ [0,1] ∧ a 14 ∈ [0,2,3,4,5] := by
  have b0 : a 7 ≠ 5 := exclude [0,3] (fun u v => edge r20 v u) (a 7) (a 5) 5 d5 c20 (by decide +kernel)
  have t0 : a 7 ∈ [0,1,2,4] := remove (a 7) 5 [0,1,2,4,5] d7 b0
  have b1 : a 13 ≠ 1 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 1 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d13 b1
  have b2 : a 13 ≠ 3 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 13) 3 [0,2,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 13 ≠ 4 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 13) 4 [0,2,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 13 ≠ 5 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,2,6,7,8,9,10,11] := remove (a 13) 5 [0,2,5,6,7,8,9,10,11] t3 b4
  have b5 : a 13 ≠ 6 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,2,7,8,9,10,11] := remove (a 13) 6 [0,2,6,7,8,9,10,11] t4 b5
  have b6 : a 13 ≠ 7 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,2,8,9,10,11] := remove (a 13) 7 [0,2,7,8,9,10,11] t5 b6
  have b7 : a 13 ≠ 8 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,2,9,10,11] := remove (a 13) 8 [0,2,8,9,10,11] t6 b7
  have b8 : a 13 ≠ 9 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 9 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,10,11] := remove (a 13) 9 [0,2,9,10,11] t7 b8
  have b9 : a 13 ≠ 10 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 10 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,2,11] := remove (a 13) 10 [0,2,10,11] t8 b9
  have b10 : a 13 ≠ 11 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 11 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,2] := remove (a 13) 11 [0,2,11] t9 b10
  have b11 : a 21 ≠ 2 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b11
  have b12 : a 21 ≠ 3 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] t11 b12
  have b13 : a 21 ≠ 4 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t12 b13
  have b14 : a 21 ≠ 5 := exclude [0,3] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t13 b14
  have b15 : a 14 ≠ 1 := exclude [0,1,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b15
  exact And.intro t0 (And.intro t10 (And.intro t14 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_196
