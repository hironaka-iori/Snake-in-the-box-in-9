import PartitionData205_179
namespace PartitionCover205_179
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2])
    (d3 : a 3 ∈ [0])
    (d6 : a 6 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0,1,13,14,15,16,17] := by
  have b0 : a 2 ≠ 1 := exclude [0] (edge r9) (a 2) (a 3) 1 d3 c9 (by decide +kernel)
  have t0 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0,1] (edge r10) (a 2) (a 6) 2 d6 c10 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 2 [0,2] t0 b1
  have b2 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b2
  have b3 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 t1 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,2] := remove (a 10) 1 [0,1,2] d10 b3
  have b4 : a 10 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 2 t1 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0] := remove (a 10) 2 [0,2] t3 b4
  have b5 : a 18 ≠ 2 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 2 t1 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d18 b5
  have b6 : a 18 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 3 t1 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 18 ≠ 4 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 4 t1 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 18 ≠ 5 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 5 t1 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 18 ≠ 6 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 6 t1 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 18 ≠ 7 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 7 t1 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 18) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 18 ≠ 8 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 8 t1 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 18) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 18 ≠ 9 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 9 t1 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 18) 9 [0,1,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 18 ≠ 10 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 10 t1 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 18) 10 [0,1,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 18 ≠ 11 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 11 t1 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,12,13,14,15,16,17] := remove (a 18) 11 [0,1,11,12,13,14,15,16,17] t13 b14
  have b15 : a 18 ≠ 12 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 12 t1 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,1,13,14,15,16,17] := remove (a 18) 12 [0,1,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t4 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,13,14,15,16,17])
    (d2 : a 2 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2])
    (d4 : a 4 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 18 ∈ [0,1,14,15] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0,1,2] ∧ a 5 ∈ [0,1] ∧ a 12 ∈ [0,1,3,5] ∧ a 20 ∈ [0,5,6,7,8,9,10,11] := by
  have b0 : a 18 ≠ 13 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 13 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,1,14,15,16,17] := remove (a 18) 13 [0,1,13,14,15,16,17] d18 b0
  have b1 : a 18 ≠ 16 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,14,15,17] := remove (a 18) 16 [0,1,14,15,16,17] t0 b1
  have b2 : a 18 ≠ 17 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,14,15] := remove (a 18) 17 [0,1,14,15,17] t1 b2
  have b3 : a 11 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b3
  have b4 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,3,4,5] := remove (a 11) 2 [0,2,3,4,5] t3 b4
  have b5 : a 11 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,4,5] := remove (a 11) 3 [0,3,4,5] t4 b5
  have b6 : a 11 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,5] := remove (a 11) 4 [0,4,5] t5 b6
  have b7 : a 11 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0] := remove (a 11) 5 [0,5] t6 b7
  have b8 : a 19 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,2] := remove (a 19) 3 [0,1,2,3] d19 b8
  have b9 : a 5 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 2 d4 c16 (by decide +kernel)
  have t9 : a 5 ∈ [0,1] := remove (a 5) 2 [0,1,2] d5 b9
  have b10 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b10
  have b11 : a 12 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,3,5] := remove (a 12) 4 [0,1,3,4,5] t10 b11
  have b12 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b12
  have b13 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 20) 2 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 20 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 20 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,5,6,7,8,9,10,11] := remove (a 20) 4 [0,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t11 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,5,6,7,8,9,10,11])
    (d4 : a 4 ∈ [0])
    (d13 : a 13 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d7 : a 7 ∈ [0,1,2])
    (d6 : a 6 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 20 ∈ [0,7,9,11] ∧ a 13 ∈ [0,1] ∧ a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] ∧ a 7 ∈ [0,2] ∧ a 14 ∈ [0,1] ∧ a 22 ∈ [0,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 20 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,6,7,8,9,10,11] := remove (a 20) 5 [0,5,6,7,8,9,10,11] d20 b0
  have b1 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,7,8,9,10,11] := remove (a 20) 6 [0,6,7,8,9,10,11] t0 b1
  have b2 : a 20 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,7,9,10,11] := remove (a 20) 8 [0,7,8,9,10,11] t1 b2
  have b3 : a 20 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,7,9,11] := remove (a 20) 10 [0,7,9,10,11] t2 b3
  have b4 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,1] := remove (a 13) 2 [0,1,2] d13 b4
  have b5 : a 21 ≠ 12 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 12 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] := remove (a 21) 12 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d21 b5
  have b6 : a 21 ≠ 13 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 13 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] := remove (a 21) 13 [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] t5 b6
  have b7 : a 21 ≠ 14 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 14 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] := remove (a 21) 14 [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] t6 b7
  have b8 : a 21 ≠ 15 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 15 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17] := remove (a 21) 15 [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] t7 b8
  have b9 : a 21 ≠ 16 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 16 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,17] := remove (a 21) 16 [0,1,2,3,4,5,6,7,8,9,10,11,16,17] t8 b9
  have b10 : a 21 ≠ 17 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 17 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] := remove (a 21) 17 [0,1,2,3,4,5,6,7,8,9,10,11,17] t9 b10
  have b11 : a 7 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 7) (a 6) 1 d6 c23 (by decide +kernel)
  have t11 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b11
  have b12 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,3] := remove (a 14) 2 [0,1,2,3] d14 b12
  have b13 : a 14 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,1] := remove (a 14) 3 [0,1,3] t12 b13
  have b14 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b14
  have b15 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t4 (And.intro t10 (And.intro t11 (And.intro t13 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 22 ∈ [0,4,6,9] ∧ a 15 ∈ [0,1,2,3] ∧ a 23 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17] := by
  have b0 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,3,4,5,6,7,8,9,10,11] d22 b0
  have b1 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,4,6,7,8,9,10,11] := remove (a 22) 5 [0,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 22 ≠ 7 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,4,6,8,9,10,11] := remove (a 22) 7 [0,4,6,7,8,9,10,11] t1 b2
  have b3 : a 22 ≠ 8 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,4,6,9,10,11] := remove (a 22) 8 [0,4,6,8,9,10,11] t2 b3
  have b4 : a 22 ≠ 10 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,4,6,9,11] := remove (a 22) 10 [0,4,6,9,10,11] t3 b4
  have b5 : a 22 ≠ 11 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,4,6,9] := remove (a 22) 11 [0,4,6,9,11] t4 b5
  have b6 : a 15 ≠ 4 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,2,3,5,6,7,8] := remove (a 15) 4 [0,1,2,3,4,5,6,7,8] d15 b6
  have b7 : a 15 ≠ 5 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,2,3,6,7,8] := remove (a 15) 5 [0,1,2,3,5,6,7,8] t6 b7
  have b8 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,2,3,7,8] := remove (a 15) 6 [0,1,2,3,6,7,8] t7 b8
  have b9 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,2,3,8] := remove (a 15) 7 [0,1,2,3,7,8] t8 b9
  have b10 : a 15 ≠ 8 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,2,3] := remove (a 15) 8 [0,1,2,3,8] t9 b10
  have b11 : a 23 ≠ 6 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 23) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d23 b11
  have b12 : a 23 ≠ 7 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 23) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 23 ≠ 8 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] := remove (a 23) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 23 ≠ 9 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17] := remove (a 23) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 23 ≠ 10 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17] := remove (a 23) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t5 (And.intro t10 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_179
