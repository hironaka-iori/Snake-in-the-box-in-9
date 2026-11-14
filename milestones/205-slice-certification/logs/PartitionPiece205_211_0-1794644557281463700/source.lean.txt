import PartitionData205_211
namespace PartitionCover205_211
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 4 ∈ [0,3] ∧ a 8 ∈ [0,3] ∧ a 16 ∈ [0,2] ∧ a 5 ∈ [0,1] ∧ a 9 ∈ [0,1,4,5,6,7,8,9] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5,6,7,8] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8] d4 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,3,4,5,6,7,8] := remove (a 4) 2 [0,2,3,4,5,6,7,8] t0 b1
  have b2 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,3,5,6,7,8] := remove (a 4) 4 [0,3,4,5,6,7,8] t1 b2
  have b3 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,3,6,7,8] := remove (a 4) 5 [0,3,5,6,7,8] t2 b3
  have b4 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,3,7,8] := remove (a 4) 6 [0,3,6,7,8] t3 b4
  have b5 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,3,8] := remove (a 4) 7 [0,3,7,8] t4 b5
  have b6 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,3] := remove (a 4) 8 [0,3,8] t5 b6
  have b7 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,2,3,4,5] := remove (a 8) 1 [0,1,2,3,4,5] d8 b7
  have b8 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,3,4,5] := remove (a 8) 2 [0,2,3,4,5] t7 b8
  have b9 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,3,5] := remove (a 8) 4 [0,3,4,5] t8 b9
  have b10 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,3] := remove (a 8) 5 [0,3,5] t9 b10
  have b11 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b11
  have b12 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t11 b12
  have b13 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,1] := remove (a 5) 2 [0,1,2] d5 b13
  have b14 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 9) 2 [0,1,2,3,4,5,6,7,8,9] d9 b14
  have b15 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,1,4,5,6,7,8,9] := remove (a 9) 3 [0,1,3,4,5,6,7,8,9] t14 b15
  exact And.intro t6 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,4,5,6,7,8,9])
    (d1 : a 1 ∈ [0,1])
    (d17 : a 17 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,3])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    : a 9 ∈ [0,1,6,7] ∧ a 17 ∈ [0,2] ∧ a 6 ∈ [0,1,6,7,14,15,16,17] := by
  have b0 : a 9 ≠ 4 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,1,5,6,7,8,9] := remove (a 9) 4 [0,1,4,5,6,7,8,9] d9 b0
  have b1 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,1,6,7,8,9] := remove (a 9) 5 [0,1,5,6,7,8,9] t0 b1
  have b2 : a 9 ≠ 8 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 8 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,1,6,7,9] := remove (a 9) 8 [0,1,6,7,8,9] t1 b2
  have b3 : a 9 ≠ 9 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 9 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,1,6,7] := remove (a 9) 9 [0,1,6,7,9] t2 b3
  have b4 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t4 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b4
  have b5 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t5 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t4 b5
  have b6 : a 6 ≠ 2 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t6 : a 6 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 6) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d6 b6
  have b7 : a 6 ≠ 3 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 3 d4 c17 (by decide +kernel)
  have t7 : a 6 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 6) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 6 ≠ 4 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 4 d4 c17 (by decide +kernel)
  have t8 : a 6 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 6) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 6 ≠ 5 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 5 d4 c17 (by decide +kernel)
  have t9 : a 6 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 6) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 6 ≠ 8 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 8 d4 c17 (by decide +kernel)
  have t10 : a 6 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 6) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 6 ≠ 9 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 9 d4 c17 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 6) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 6 ≠ 10 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 10 d4 c17 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 6) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 6 ≠ 11 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 11 d4 c17 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 6) 11 [0,1,6,7,11,12,13,14,15,16,17] t12 b13
  have b14 : a 6 ≠ 12 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 12 d4 c17 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,6,7,13,14,15,16,17] := remove (a 6) 12 [0,1,6,7,12,13,14,15,16,17] t13 b14
  have b15 : a 6 ≠ 13 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 13 d4 c17 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,6,7,14,15,16,17] := remove (a 6) 13 [0,1,6,7,13,14,15,16,17] t14 b15
  exact And.intro t3 (And.intro t5 (t15))

theorem chunk2 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,6,7,14,15,16,17])
    (d4 : a 4 ∈ [0,3])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8])
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 6 ∈ [0,1,6,7] ∧ a 12 ∈ [0,2] ∧ a 20 ∈ [0,3,4,5,6,7,8] := by
  have b0 : a 6 ≠ 14 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 14 d4 c17 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,6,7,15,16,17] := remove (a 6) 14 [0,1,6,7,14,15,16,17] d6 b0
  have b1 : a 6 ≠ 15 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 15 d4 c17 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,6,7,16,17] := remove (a 6) 15 [0,1,6,7,15,16,17] t0 b1
  have b2 : a 6 ≠ 16 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 16 d4 c17 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,6,7,17] := remove (a 6) 16 [0,1,6,7,16,17] t1 b2
  have b3 : a 6 ≠ 17 := exclude [0,3] (fun u v => edge r17 v u) (a 6) (a 4) 17 d4 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,6,7] := remove (a 6) 17 [0,1,6,7,17] t2 b3
  have b4 : a 12 ≠ 1 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b4
  have b5 : a 12 ≠ 3 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 12) 3 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 12 ≠ 4 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 12) 4 [0,2,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 12 ≠ 5 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,2,6,7,8,9,10,11] := remove (a 12) 5 [0,2,5,6,7,8,9,10,11] t6 b7
  have b8 : a 12 ≠ 6 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,2,7,8,9,10,11] := remove (a 12) 6 [0,2,6,7,8,9,10,11] t7 b8
  have b9 : a 12 ≠ 7 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,2,8,9,10,11] := remove (a 12) 7 [0,2,7,8,9,10,11] t8 b9
  have b10 : a 12 ≠ 8 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,2,9,10,11] := remove (a 12) 8 [0,2,8,9,10,11] t9 b10
  have b11 : a 12 ≠ 9 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,10,11] := remove (a 12) 9 [0,2,9,10,11] t10 b11
  have b12 : a 12 ≠ 10 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 10 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,2,11] := remove (a 12) 10 [0,2,10,11] t11 b12
  have b13 : a 12 ≠ 11 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 11 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,2] := remove (a 12) 11 [0,2,11] t12 b13
  have b14 : a 20 ≠ 1 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,2,3,4,5,6,7,8] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8] d20 b14
  have b15 : a 20 ≠ 2 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,3,4,5,6,7,8] := remove (a 20) 2 [0,2,3,4,5,6,7,8] t14 b15
  exact And.intro t3 (And.intro t13 (t15))

theorem chunk3 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,3,4,5,6,7,8])
    (d4 : a 4 ∈ [0,3])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8])
    (d6 : a 6 ∈ [0,1,6,7])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 20 ∈ [0] ∧ a 7 ∈ [0,1,2,4] ∧ a 13 ∈ [0,3,6,8] ∧ a 21 ∈ [0,1,2,4] ∧ a 14 ∈ [0,1,3,4,5,6,7,8] := by
  have b0 : a 20 ≠ 3 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,4,5,6,7,8] := remove (a 20) 3 [0,3,4,5,6,7,8] d20 b0
  have b1 : a 20 ≠ 4 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,5,6,7,8] := remove (a 20) 4 [0,4,5,6,7,8] t0 b1
  have b2 : a 20 ≠ 5 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,6,7,8] := remove (a 20) 5 [0,5,6,7,8] t1 b2
  have b3 : a 20 ≠ 6 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,7,8] := remove (a 20) 6 [0,6,7,8] t2 b3
  have b4 : a 20 ≠ 7 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,8] := remove (a 20) 7 [0,7,8] t3 b4
  have b5 : a 20 ≠ 8 := exclude [0,3] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0] := remove (a 20) 8 [0,8] t4 b5
  have b6 : a 7 ≠ 3 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 3 d5 c20 (by decide +kernel)
  have t6 : a 7 ∈ [0,1,2,4,5] := remove (a 7) 3 [0,1,2,3,4,5] d7 b6
  have b7 : a 7 ≠ 5 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 5 d5 c20 (by decide +kernel)
  have t7 : a 7 ∈ [0,1,2,4] := remove (a 7) 5 [0,1,2,4,5] t6 b7
  have b8 : a 13 ≠ 1 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 1 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,3,4,5,6,7,8] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8] d13 b8
  have b9 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,3,4,5,6,7,8] := remove (a 13) 2 [0,2,3,4,5,6,7,8] t8 b9
  have b10 : a 13 ≠ 4 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,3,5,6,7,8] := remove (a 13) 4 [0,3,4,5,6,7,8] t9 b10
  have b11 : a 13 ≠ 5 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,3,6,7,8] := remove (a 13) 5 [0,3,5,6,7,8] t10 b11
  have b12 : a 13 ≠ 7 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,3,6,8] := remove (a 13) 7 [0,3,6,7,8] t11 b12
  have b13 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,2,4,5] := remove (a 21) 3 [0,1,2,3,4,5] d21 b13
  have b14 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,1,2,4] := remove (a 21) 5 [0,1,2,4,5] t13 b14
  have b15 : a 14 ≠ 2 := exclude [0,1,6,7] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,3,4,5,6,7,8] := remove (a 14) 2 [0,1,2,3,4,5,6,7,8] d14 b15
  exact And.intro t5 (And.intro t7 (And.intro t12 (And.intro t14 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_211
