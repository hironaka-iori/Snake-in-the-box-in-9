import PartitionData205_207
namespace PartitionCover205_207
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8])
    (d16 : a 16 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 2 ∈ [0,3] ∧ a 8 ∈ [0,2] ∧ a 16 ∈ [0,1] ∧ a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5] := remove (a 2) 1 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5] := remove (a 2) 2 [0,2,3,4,5] t0 b1
  have b2 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,3,5] := remove (a 2) 4 [0,3,4,5] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,3] := remove (a 2) 5 [0,3,5] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3,4,5,6,7,8] := remove (a 8) 1 [0,1,2,3,4,5,6,7,8] d8 b4
  have b5 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,2,4,5,6,7,8] := remove (a 8) 3 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,2,5,6,7,8] := remove (a 8) 4 [0,2,4,5,6,7,8] t5 b6
  have b7 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,2,6,7,8] := remove (a 8) 5 [0,2,5,6,7,8] t6 b7
  have b8 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t8 : a 8 ∈ [0,2,7,8] := remove (a 8) 6 [0,2,6,7,8] t7 b8
  have b9 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t9 : a 8 ∈ [0,2,8] := remove (a 8) 7 [0,2,7,8] t8 b9
  have b10 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,2] := remove (a 8) 8 [0,2,8] t9 b10
  have b11 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,3,4,5] := remove (a 16) 2 [0,1,2,3,4,5] d16 b11
  have b12 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,4,5] := remove (a 16) 3 [0,1,3,4,5] t11 b12
  have b13 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,5] := remove (a 16) 4 [0,1,4,5] t12 b13
  have b14 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,1] := remove (a 16) 5 [0,1,5] t13 b14
  have b15 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 9) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d9 b15
  exact And.intro t3 (And.intro t10 (And.intro t14 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0,3])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8])
    (d18 : a 18 ∈ [0,1,2])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 9 ∈ [0,2,4,6,8,10] ∧ a 6 ∈ [0,3] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0,2] := by
  have b0 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 9) 3 [0,2,3,4,5,6,7,8,9,10,11] d9 b0
  have b1 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 5 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0,2,4,6,7,8,9,10,11] := remove (a 9) 5 [0,2,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 9 ≠ 7 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 7 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0,2,4,6,8,9,10,11] := remove (a 9) 7 [0,2,4,6,7,8,9,10,11] t1 b2
  have b3 : a 9 ≠ 9 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 9 d1 c7 (by decide +kernel)
  have t3 : a 9 ∈ [0,2,4,6,8,10,11] := remove (a 9) 9 [0,2,4,6,8,9,10,11] t2 b3
  have b4 : a 9 ≠ 11 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 11 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,4,6,8,10] := remove (a 9) 11 [0,2,4,6,8,10,11] t3 b4
  have b5 : a 6 ≠ 1 := exclude [0,3] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b5
  have b6 : a 6 ≠ 2 := exclude [0,3] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t6 : a 6 ∈ [0,3] := remove (a 6) 2 [0,2,3] t5 b6
  have b7 : a 10 ≠ 1 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,2,3,4,5,6,7,8] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8] d10 b7
  have b8 : a 10 ≠ 2 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,3,4,5,6,7,8] := remove (a 10) 2 [0,2,3,4,5,6,7,8] t7 b8
  have b9 : a 10 ≠ 3 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,4,5,6,7,8] := remove (a 10) 3 [0,3,4,5,6,7,8] t8 b9
  have b10 : a 10 ≠ 4 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,5,6,7,8] := remove (a 10) 4 [0,4,5,6,7,8] t9 b10
  have b11 : a 10 ≠ 5 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,6,7,8] := remove (a 10) 5 [0,5,6,7,8] t10 b11
  have b12 : a 10 ≠ 6 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,7,8] := remove (a 10) 6 [0,6,7,8] t11 b12
  have b13 : a 10 ≠ 7 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,8] := remove (a 10) 7 [0,7,8] t12 b13
  have b14 : a 10 ≠ 8 := exclude [0,3] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0] := remove (a 10) 8 [0,8] t13 b14
  have b15 : a 18 ≠ 1 := exclude [0,3] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,2] := remove (a 18) 1 [0,1,2] d18 b15
  exact And.intro t4 (And.intro t6 (And.intro t14 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2])
    (d2 : a 2 ∈ [0,3])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d3 : a 3 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8])
    (d4 : a 4 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2])
    (d6 : a 6 ∈ [0,3])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 18 ∈ [0] ∧ a 11 ∈ [0,1,2,3,6,7,10,11] ∧ a 12 ∈ [0,1,5,7] ∧ a 20 ∈ [0,1,3,5] ∧ a 7 ∈ [0,3] ∧ a 14 ∈ [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 18 ≠ 2 := exclude [0,3] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b0
  have b1 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 11) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b1
  have b2 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 11) 5 [0,1,2,3,5,6,7,8,9,10,11] t1 b2
  have b3 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,1,2,3,6,7,9,10,11] := remove (a 11) 8 [0,1,2,3,6,7,8,9,10,11] t2 b3
  have b4 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,1,2,3,6,7,10,11] := remove (a 11) 9 [0,1,2,3,6,7,9,10,11] t3 b4
  have b5 : a 12 ≠ 2 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,3,4,5,6,7,8] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8] d12 b5
  have b6 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,4,5,6,7,8] := remove (a 12) 3 [0,1,3,4,5,6,7,8] t5 b6
  have b7 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,5,6,7,8] := remove (a 12) 4 [0,1,4,5,6,7,8] t6 b7
  have b8 : a 12 ≠ 6 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,5,7,8] := remove (a 12) 6 [0,1,5,6,7,8] t7 b8
  have b9 : a 12 ≠ 8 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,5,7] := remove (a 12) 8 [0,1,5,7,8] t8 b9
  have b10 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,3,4,5] := remove (a 20) 2 [0,1,2,3,4,5] d20 b10
  have b11 : a 20 ≠ 4 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,3,5] := remove (a 20) 4 [0,1,3,4,5] t10 b11
  have b12 : a 7 ≠ 1 := exclude [0,1,2] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t12 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b12
  have b13 : a 7 ≠ 2 := exclude [0,3] (fun u v => edge r23 v u) (a 7) (a 6) 2 d6 c23 (by decide +kernel)
  have t13 : a 7 ∈ [0,3] := remove (a 7) 2 [0,2,3] t12 b13
  have b14 : a 14 ≠ 2 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b14
  have b15 : a 14 ≠ 4 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 4 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t9 (And.intro t11 (And.intro t13 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d6 : a 6 ∈ [0,3])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,3])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 14 ∈ [0,1,3,5,6,11,12,17] ∧ a 15 ∈ [0,2] ∧ a 23 ∈ [0,1,2,3,5,7,9,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 14 ≠ 7 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,3,5,6,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b0
  have b1 : a 14 ≠ 8 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,3,5,6,9,10,11,12,13,14,15,16,17] := remove (a 14) 8 [0,1,3,5,6,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 14 ≠ 9 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,3,5,6,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,1,3,5,6,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 14 ≠ 10 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,3,5,6,11,12,13,14,15,16,17] := remove (a 14) 10 [0,1,3,5,6,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 14 ≠ 13 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 13 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,3,5,6,11,12,14,15,16,17] := remove (a 14) 13 [0,1,3,5,6,11,12,13,14,15,16,17] t3 b4
  have b5 : a 14 ≠ 14 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 14 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,3,5,6,11,12,15,16,17] := remove (a 14) 14 [0,1,3,5,6,11,12,14,15,16,17] t4 b5
  have b6 : a 14 ≠ 15 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,3,5,6,11,12,16,17] := remove (a 14) 15 [0,1,3,5,6,11,12,15,16,17] t5 b6
  have b7 : a 14 ≠ 16 := exclude [0,3] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,3,5,6,11,12,17] := remove (a 14) 16 [0,1,3,5,6,11,12,16,17] t6 b7
  have b8 : a 15 ≠ 1 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 1 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,2,3,4,5] := remove (a 15) 1 [0,1,2,3,4,5] d15 b8
  have b9 : a 15 ≠ 3 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,2,4,5] := remove (a 15) 3 [0,2,3,4,5] t8 b9
  have b10 : a 15 ≠ 4 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0,2,5] := remove (a 15) 4 [0,2,4,5] t9 b10
  have b11 : a 15 ≠ 5 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t11 : a 15 ∈ [0,2] := remove (a 15) 5 [0,2,5] t10 b11
  have b12 : a 23 ≠ 4 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 23) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d23 b12
  have b13 : a 23 ≠ 6 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,2,3,5,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 23) 6 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 23 ≠ 8 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,2,3,5,7,9,10,11,12,13,14,15,16,17,18,19] := remove (a 23) 8 [0,1,2,3,5,7,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 23 ≠ 10 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,2,3,5,7,9,11,12,13,14,15,16,17,18,19] := remove (a 23) 10 [0,1,2,3,5,7,9,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t7 (And.intro t11 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_207
