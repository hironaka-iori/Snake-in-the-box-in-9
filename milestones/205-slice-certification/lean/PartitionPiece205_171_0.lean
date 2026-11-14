import PartitionData205_171
namespace PartitionCover205_171
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7])
    (d16 : a 16 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    : a 2 ∈ [0,2] ∧ a 4 ∈ [0,1] ∧ a 8 ∈ [0,4] ∧ a 16 ∈ [0,2] ∧ a 6 ∈ [0,2,4,5,6,7,8,9,10,11] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,3,4,5] := remove (a 4) 2 [0,1,2,3,4,5] d4 b2
  have b3 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,4,5] := remove (a 4) 3 [0,1,3,4,5] t2 b3
  have b4 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,1,5] := remove (a 4) 4 [0,1,4,5] t3 b4
  have b5 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,1] := remove (a 4) 5 [0,1,5] t4 b5
  have b6 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,2,3,4,5,6,7] := remove (a 8) 1 [0,1,2,3,4,5,6,7] d8 b6
  have b7 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,3,4,5,6,7] := remove (a 8) 2 [0,2,3,4,5,6,7] t6 b7
  have b8 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,4,5,6,7] := remove (a 8) 3 [0,3,4,5,6,7] t7 b8
  have b9 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,4,6,7] := remove (a 8) 5 [0,4,5,6,7] t8 b9
  have b10 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,4,7] := remove (a 8) 6 [0,4,6,7] t9 b10
  have b11 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,4] := remove (a 8) 7 [0,4,7] t10 b11
  have b12 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b12
  have b13 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t12 b13
  have b14 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 1 t1 c10 (by decide +kernel)
  have t14 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d6 b14
  have b15 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 3 t1 c10 (by decide +kernel)
  have t15 : a 6 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 6) 3 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t11 (And.intro t13 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,2,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (d3 : a 3 ∈ [0])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 6 ∈ [0,2,7,11] ∧ a 10 ∈ [0,4] ∧ a 11 ∈ [0,2,6,7,8] := by
  have b0 : a 6 ≠ 4 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 6) 4 [0,2,4,5,6,7,8,9,10,11] d6 b0
  have b1 : a 6 ≠ 5 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 5 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,6,7,8,9,10,11] := remove (a 6) 5 [0,2,5,6,7,8,9,10,11] t0 b1
  have b2 : a 6 ≠ 6 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 6 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,2,7,8,9,10,11] := remove (a 6) 6 [0,2,6,7,8,9,10,11] t1 b2
  have b3 : a 6 ≠ 8 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 8 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,2,7,9,10,11] := remove (a 6) 8 [0,2,7,8,9,10,11] t2 b3
  have b4 : a 6 ≠ 9 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 9 d2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,2,7,10,11] := remove (a 6) 9 [0,2,7,9,10,11] t3 b4
  have b5 : a 6 ≠ 10 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 10 d2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,7,11] := remove (a 6) 10 [0,2,7,10,11] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3,4,5,6,7] := remove (a 10) 1 [0,1,2,3,4,5,6,7] d10 b6
  have b7 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,3,4,5,6,7] := remove (a 10) 2 [0,2,3,4,5,6,7] t6 b7
  have b8 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,4,5,6,7] := remove (a 10) 3 [0,3,4,5,6,7] t7 b8
  have b9 : a 10 ≠ 5 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,4,6,7] := remove (a 10) 5 [0,4,5,6,7] t8 b9
  have b10 : a 10 ≠ 6 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,4,7] := remove (a 10) 6 [0,4,6,7] t9 b10
  have b11 : a 10 ≠ 7 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,4] := remove (a 10) 7 [0,4,7] t10 b11
  have b12 : a 11 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,2,3,4,5,6,7,8] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8] d11 b12
  have b13 : a 11 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,4,5,6,7,8] := remove (a 11) 3 [0,2,3,4,5,6,7,8] t12 b13
  have b14 : a 11 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,5,6,7,8] := remove (a 11) 4 [0,2,4,5,6,7,8] t13 b14
  have b15 : a 11 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,6,7,8] := remove (a 11) 5 [0,2,5,6,7,8] t14 b15
  exact And.intro t5 (And.intro t11 (t15))

theorem chunk2 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,6,7,8])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,2,7,11])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1,2])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 11 ∈ [0,2,6,8] ∧ a 5 ∈ [0,4] ∧ a 6 ∈ [0,2] ∧ a 12 ∈ [0,1] ∧ a 20 ∈ [0,3] ∧ a 13 ∈ [0,2] := by
  have b0 : a 11 ≠ 7 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,6,8] := remove (a 11) 7 [0,2,6,7,8] d11 b0
  have b1 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t1 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b1
  have b2 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,4,5] := remove (a 5) 3 [0,2,3,4,5] t1 b2
  have b3 : a 6 ≠ 7 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 7 d4 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0,2,11] := remove (a 6) 7 [0,2,7,11] d6 b3
  have b4 : a 6 ≠ 11 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 11 d4 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0,2] := remove (a 6) 11 [0,2,11] t3 b4
  have b5 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b5
  have b6 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,4,5] := remove (a 12) 3 [0,1,3,4,5] t5 b6
  have b7 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,5] := remove (a 12) 4 [0,1,4,5] t6 b7
  have b8 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1] := remove (a 12) 5 [0,1,5] t7 b8
  have b9 : a 20 ≠ 1 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,2,3,4,5] := remove (a 20) 1 [0,1,2,3,4,5] d20 b9
  have b10 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,3,4,5] := remove (a 20) 2 [0,2,3,4,5] t9 b10
  have b11 : a 20 ≠ 4 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,3,5] := remove (a 20) 4 [0,3,4,5] t10 b11
  have b12 : a 20 ≠ 5 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,3] := remove (a 20) 5 [0,3,5] t11 b12
  have b13 : a 5 ≠ 2 := exclude [0,1,2] (edge r21) (a 5) (a 13) 2 d13 c21 (by decide +kernel)
  have t13 : a 5 ∈ [0,4,5] := remove (a 5) 2 [0,2,4,5] t2 b13
  have b14 : a 5 ≠ 5 := exclude [0,1,2] (edge r21) (a 5) (a 13) 5 d13 c21 (by decide +kernel)
  have t14 : a 5 ∈ [0,4] := remove (a 5) 5 [0,4,5] t13 b14
  have b15 : a 13 ≠ 1 := exclude [0,4] (fun u v => edge r21 v u) (a 13) (a 5) 1 t14 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,2] := remove (a 13) 1 [0,1,2] d13 b15
  exact And.intro t0 (And.intro t14 (And.intro t4 (And.intro t8 (And.intro t12 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,2])
    (d5 : a 5 ∈ [0,4])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,2])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,4])
    (d11 : a 11 ∈ [0,2,6,8])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 22 ∈ [0,1,2] ∧ a 9 ∈ [0,3] ∧ a 11 ∈ [0,6] ∧ a 25 ∈ [0,2,3,4,5] := by
  have b0 : a 13 ≠ 2 := exclude [0,4] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b0
  have b1 : a 21 ≠ 1 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b1
  have b2 : a 21 ≠ 2 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t1 b2
  have b3 : a 21 ≠ 3 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,4,5] := remove (a 21) 3 [0,3,4,5] t2 b3
  have b4 : a 21 ≠ 4 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,5] := remove (a 21) 4 [0,4,5] t3 b4
  have b5 : a 21 ≠ 5 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 5 [0,5] t4 b5
  have b6 : a 22 ≠ 3 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,1,2,4,5] := remove (a 22) 3 [0,1,2,3,4,5] d22 b6
  have b7 : a 22 ≠ 4 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,1,2,5] := remove (a 22) 4 [0,1,2,4,5] t6 b7
  have b8 : a 22 ≠ 5 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,2] := remove (a 22) 5 [0,1,2,5] t7 b8
  have b9 : a 9 ≠ 1 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 1 d8 c28 (by decide +kernel)
  have t9 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b9
  have b10 : a 9 ≠ 2 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 2 d8 c28 (by decide +kernel)
  have t10 : a 9 ∈ [0,3,4,5] := remove (a 9) 2 [0,2,3,4,5] t9 b10
  have b11 : a 9 ≠ 4 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t11 : a 9 ∈ [0,3,5] := remove (a 9) 4 [0,3,4,5] t10 b11
  have b12 : a 9 ≠ 5 := exclude [0,4] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t12 : a 9 ∈ [0,3] := remove (a 9) 5 [0,3,5] t11 b12
  have b13 : a 11 ≠ 2 := exclude [0,3] (fun u v => edge r32 v u) (a 11) (a 9) 2 t12 c32 (by decide +kernel)
  have t13 : a 11 ∈ [0,6,8] := remove (a 11) 2 [0,2,6,8] d11 b13
  have b14 : a 11 ≠ 8 := exclude [0,3] (fun u v => edge r32 v u) (a 11) (a 9) 8 t12 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0,6] := remove (a 11) 8 [0,6,8] t13 b14
  have b15 : a 25 ≠ 1 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 1 t12 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,2,3,4,5] := remove (a 25) 1 [0,1,2,3,4,5] d25 b15
  exact And.intro t0 (And.intro t5 (And.intro t8 (And.intro t12 (And.intro t14 (t15)))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_171
