import PartitionData205_199
namespace PartitionCover205_199
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (d1 : a 1 ∈ [0])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 2 ∈ [0,1] ∧ a 4 ∈ [0,2] ∧ a 16 ∈ [0,3] ∧ a 9 ∈ [0,4] := by
  have b0 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,1,3,4,5] := remove (a 2) 2 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,1,4,5] := remove (a 2) 3 [0,1,3,4,5] t0 b1
  have b2 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,1,5] := remove (a 2) 4 [0,1,4,5] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,1] := remove (a 2) 5 [0,1,5] t2 b3
  have b4 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b4
  have b5 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t4 b5
  have b6 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,2,3,4,5] := remove (a 16) 1 [0,1,2,3,4,5] d16 b6
  have b7 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,3,4,5] := remove (a 16) 2 [0,2,3,4,5] t6 b7
  have b8 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,3,5] := remove (a 16) 4 [0,3,4,5] t7 b8
  have b9 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,3] := remove (a 16) 5 [0,3,5] t8 b9
  have b10 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t10 : a 9 ∈ [0,2,3,4,5,6,7] := remove (a 9) 1 [0,1,2,3,4,5,6,7] d9 b10
  have b11 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t11 : a 9 ∈ [0,3,4,5,6,7] := remove (a 9) 2 [0,2,3,4,5,6,7] t10 b11
  have b12 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t12 : a 9 ∈ [0,4,5,6,7] := remove (a 9) 3 [0,3,4,5,6,7] t11 b12
  have b13 : a 9 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t13 : a 9 ∈ [0,4,6,7] := remove (a 9) 5 [0,4,5,6,7] t12 b13
  have b14 : a 9 ≠ 6 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 6 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,4,7] := remove (a 9) 6 [0,4,6,7] t13 b14
  have b15 : a 9 ≠ 7 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,4] := remove (a 9) 7 [0,4,7] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t9 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0])
    (d3 : a 3 ∈ [0,1,2,3,4,5])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,1,2])
    (d18 : a 18 ∈ [0,1,2])
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 17 ∈ [0,5,6,11] ∧ a 3 ∈ [0,1] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0,1] ∧ a 18 ∈ [0,2] := by
  have b0 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t0 : a 17 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d17 b0
  have b1 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 17) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 17) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 17 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0,5,6,7,8,9,10,11] := remove (a 17) 4 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 17 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 7 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,5,6,8,9,10,11] := remove (a 17) 7 [0,5,6,7,8,9,10,11] t3 b4
  have b5 : a 17 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 8 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,5,6,9,10,11] := remove (a 17) 8 [0,5,6,8,9,10,11] t4 b5
  have b6 : a 17 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 9 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,5,6,10,11] := remove (a 17) 9 [0,5,6,9,10,11] t5 b6
  have b7 : a 17 ≠ 10 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 10 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,5,6,11] := remove (a 17) 10 [0,5,6,10,11] t6 b7
  have b8 : a 3 ≠ 2 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 2 d2 c9 (by decide +kernel)
  have t8 : a 3 ∈ [0,1,3,4,5] := remove (a 3) 2 [0,1,2,3,4,5] d3 b8
  have b9 : a 3 ≠ 3 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t9 : a 3 ∈ [0,1,4,5] := remove (a 3) 3 [0,1,3,4,5] t8 b9
  have b10 : a 3 ≠ 4 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 4 d2 c9 (by decide +kernel)
  have t10 : a 3 ∈ [0,1,5] := remove (a 3) 4 [0,1,4,5] t9 b10
  have b11 : a 3 ≠ 5 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 5 d2 c9 (by decide +kernel)
  have t11 : a 3 ∈ [0,1] := remove (a 3) 5 [0,1,5] t10 b11
  have b12 : a 6 ≠ 1 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,2] := remove (a 6) 1 [0,1,2] d6 b12
  have b13 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t13 : a 6 ∈ [0] := remove (a 6) 2 [0,2] t12 b13
  have b14 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,1] := remove (a 10) 2 [0,1,2] d10 b14
  have b15 : a 18 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,2] := remove (a 18) 1 [0,1,2] d18 b15
  exact And.intro t7 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2])
    (d2 : a 2 ∈ [0,1])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,2])
    (d12 : a 12 ∈ [0,1,2,3])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 18 ∈ [0] ∧ a 7 ∈ [0,1] ∧ a 11 ∈ [0,1,2] ∧ a 5 ∈ [0,1] ∧ a 12 ∈ [0,2,3] := by
  have b0 : a 18 ≠ 2 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b0
  have b1 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t1 : a 7 ∈ [0,1,3,4,5] := remove (a 7) 2 [0,1,2,3,4,5] d7 b1
  have b2 : a 7 ≠ 3 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 3 d3 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0,1,4,5] := remove (a 7) 3 [0,1,3,4,5] t1 b2
  have b3 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 4 d3 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0,1,5] := remove (a 7) 4 [0,1,4,5] t2 b3
  have b4 : a 7 ≠ 5 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 5 d3 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0,1] := remove (a 7) 5 [0,1,5] t3 b4
  have b5 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,1,2,4,5,6,7,8] := remove (a 11) 3 [0,1,2,3,4,5,6,7,8] d11 b5
  have b6 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,1,2,5,6,7,8] := remove (a 11) 4 [0,1,2,4,5,6,7,8] t5 b6
  have b7 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,1,2,6,7,8] := remove (a 11) 5 [0,1,2,5,6,7,8] t6 b7
  have b8 : a 11 ≠ 6 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,2,7,8] := remove (a 11) 6 [0,1,2,6,7,8] t7 b8
  have b9 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,2,8] := remove (a 11) 7 [0,1,2,7,8] t8 b9
  have b10 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,1,2] := remove (a 11) 8 [0,1,2,8] t9 b10
  have b11 : a 5 ≠ 2 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 2 d4 c16 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,3,4,5] := remove (a 5) 2 [0,1,2,3,4,5] d5 b11
  have b12 : a 5 ≠ 3 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,4,5] := remove (a 5) 3 [0,1,3,4,5] t11 b12
  have b13 : a 5 ≠ 4 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,5] := remove (a 5) 4 [0,1,4,5] t12 b13
  have b14 : a 5 ≠ 5 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 5 d4 c16 (by decide +kernel)
  have t14 : a 5 ∈ [0,1] := remove (a 5) 5 [0,1,5] t13 b14
  have b15 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b15
  exact And.intro t0 (And.intro t4 (And.intro t10 (And.intro t14 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,2,3])
    (d4 : a 4 ∈ [0,2])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1,2])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 12 ∈ [0,2] ∧ a 20 ∈ [0,1] ∧ a 13 ∈ [0,1] ∧ a 21 ∈ [0,3] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0,2,3,4,5] := by
  have b0 : a 12 ≠ 3 := exclude [0,2] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] d12 b0
  have b1 : a 20 ≠ 2 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,3,4,5] := remove (a 20) 2 [0,1,2,3,4,5] d20 b1
  have b2 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,4,5] := remove (a 20) 3 [0,1,3,4,5] t1 b2
  have b3 : a 20 ≠ 4 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,5] := remove (a 20) 4 [0,1,4,5] t2 b3
  have b4 : a 20 ≠ 5 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,1] := remove (a 20) 5 [0,1,5] t3 b4
  have b5 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b5
  have b6 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,4,5] := remove (a 13) 3 [0,1,3,4,5] t5 b6
  have b7 : a 13 ≠ 4 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,5] := remove (a 13) 4 [0,1,4,5] t6 b7
  have b8 : a 13 ≠ 5 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,1] := remove (a 13) 5 [0,1,5] t7 b8
  have b9 : a 21 ≠ 1 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b9
  have b10 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t9 b10
  have b11 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0,3,5] := remove (a 21) 4 [0,3,4,5] t10 b11
  have b12 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0,3] := remove (a 21) 5 [0,3,5] t11 b12
  have b13 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,2] := remove (a 14) 1 [0,1,2] d14 b13
  have b14 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0] := remove (a 14) 2 [0,2] t13 b14
  have b15 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b15
  exact And.intro t0 (And.intro t4 (And.intro t8 (And.intro t12 (And.intro t14 (t15)))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_199
