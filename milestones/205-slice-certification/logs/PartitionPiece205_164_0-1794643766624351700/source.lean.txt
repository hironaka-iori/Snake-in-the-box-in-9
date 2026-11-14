import PartitionData205_164
namespace PartitionCover205_164
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    : a 4 ∈ [0,2,4,7] ∧ a 8 ∈ [0,1,2,4] ∧ a 5 ∈ [0,1,3,9] ∧ a 9 ∈ [0,1,3,4,5] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5,6,7,8] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2,4,5,6,7,8] := remove (a 4) 3 [0,2,3,4,5,6,7,8] t0 b1
  have b2 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,4,6,7,8] := remove (a 4) 5 [0,2,4,5,6,7,8] t1 b2
  have b3 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2,4,7,8] := remove (a 4) 6 [0,2,4,6,7,8] t2 b3
  have b4 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,4,7] := remove (a 4) 8 [0,2,4,7,8] t3 b4
  have b5 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,2,4,5] := remove (a 8) 3 [0,1,2,3,4,5] d8 b5
  have b6 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,2,4] := remove (a 8) 5 [0,1,2,4,5] t5 b6
  have b7 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 5) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d5 b7
  have b8 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,3,5,6,7,8,9,10,11] := remove (a 5) 4 [0,1,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t9 : a 5 ∈ [0,1,3,6,7,8,9,10,11] := remove (a 5) 5 [0,1,3,5,6,7,8,9,10,11] t8 b9
  have b10 : a 5 ≠ 6 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 6 d1 c6 (by decide +kernel)
  have t10 : a 5 ∈ [0,1,3,7,8,9,10,11] := remove (a 5) 6 [0,1,3,6,7,8,9,10,11] t9 b10
  have b11 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 7 d1 c6 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,3,8,9,10,11] := remove (a 5) 7 [0,1,3,7,8,9,10,11] t10 b11
  have b12 : a 5 ≠ 8 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 8 d1 c6 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,3,9,10,11] := remove (a 5) 8 [0,1,3,8,9,10,11] t11 b12
  have b13 : a 5 ≠ 10 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 10 d1 c6 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,3,9,11] := remove (a 5) 10 [0,1,3,9,10,11] t12 b13
  have b14 : a 5 ≠ 11 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 11 d1 c6 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,3,9] := remove (a 5) 11 [0,1,3,9,11] t13 b14
  have b15 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t15 : a 9 ∈ [0,1,3,4,5] := remove (a 9) 2 [0,1,2,3,4,5] d9 b15
  exact And.intro t4 (And.intro t6 (And.intro t14 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,3,4,5])
    (d1 : a 1 ∈ [0,1])
    (d2 : a 2 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8])
    (d18 : a 18 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d3 : a 3 ∈ [0])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 9 ∈ [0,1,3,5] ∧ a 2 ∈ [0,1] ∧ a 6 ∈ [0,2] ∧ a 18 ∈ [0,2] ∧ a 11 ∈ [0,1,3,4,5,7,8,9,11,12,14,15,16,17] := by
  have b0 : a 9 ≠ 4 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0,1,3,5] := remove (a 9) 4 [0,1,3,4,5] d9 b0
  have b1 : a 2 ≠ 2 := exclude [0,1,2,3,4,5,6,7,8] (edge r10) (a 2) (a 6) 2 d6 c10 (by decide +kernel)
  have t1 : a 2 ∈ [0,1,3] := remove (a 2) 2 [0,1,2,3] d2 b1
  have b2 : a 2 ≠ 3 := exclude [0,1,2,3,4,5,6,7,8] (edge r10) (a 2) (a 6) 3 d6 c10 (by decide +kernel)
  have t2 : a 2 ∈ [0,1] := remove (a 2) 3 [0,1,3] t1 b2
  have b3 : a 6 ≠ 1 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 1 t2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,2,3,4,5,6,7,8] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8] d6 b3
  have b4 : a 6 ≠ 3 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 3 t2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,2,4,5,6,7,8] := remove (a 6) 3 [0,2,3,4,5,6,7,8] t3 b4
  have b5 : a 6 ≠ 4 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 4 t2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,5,6,7,8] := remove (a 6) 4 [0,2,4,5,6,7,8] t4 b5
  have b6 : a 6 ≠ 5 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 5 t2 c10 (by decide +kernel)
  have t6 : a 6 ∈ [0,2,6,7,8] := remove (a 6) 5 [0,2,5,6,7,8] t5 b6
  have b7 : a 6 ≠ 6 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 6 t2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,2,7,8] := remove (a 6) 6 [0,2,6,7,8] t6 b7
  have b8 : a 6 ≠ 7 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 7 t2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,2,8] := remove (a 6) 7 [0,2,7,8] t7 b8
  have b9 : a 6 ≠ 8 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 8 t2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,2] := remove (a 6) 8 [0,2,8] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 1 t2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b10
  have b11 : a 18 ≠ 3 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 3 t2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] t10 b11
  have b12 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d11 b12
  have b13 : a 11 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,1,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 6 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 11 ≠ 10 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,1,3,4,5,7,8,9,11,12,13,14,15,16,17] := remove (a 11) 10 [0,1,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 11 ≠ 13 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 13 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,1,3,4,5,7,8,9,11,12,14,15,16,17] := remove (a 11) 13 [0,1,3,4,5,7,8,9,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t9 (And.intro t11 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,3,4,5,7,8,9,11,12,14,15,16,17])
    (d3 : a 3 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,2,4,7])
    (d5 : a 5 ∈ [0,1,3,9])
    (d12 : a 12 ∈ [0,1,2])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    : a 11 ∈ [0,1,3,4,5,7,8,9,11,12,14,16] ∧ a 19 ∈ [0,2] ∧ a 4 ∈ [0,2] ∧ a 5 ∈ [0,1] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0,1,2,4,5,6,8,10] ∧ a 7 ∈ [0,1,3,5] := by
  have b0 : a 11 ≠ 15 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 15 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,1,3,4,5,7,8,9,11,12,14,16,17] := remove (a 11) 15 [0,1,3,4,5,7,8,9,11,12,14,15,16,17] d11 b0
  have b1 : a 11 ≠ 17 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 17 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,1,3,4,5,7,8,9,11,12,14,16] := remove (a 11) 17 [0,1,3,4,5,7,8,9,11,12,14,16,17] t0 b1
  have b2 : a 19 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b2
  have b3 : a 19 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,2] := remove (a 19) 3 [0,2,3] t2 b3
  have b4 : a 4 ≠ 4 := exclude [0,1,3,9] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,7] := remove (a 4) 4 [0,2,4,7] d4 b4
  have b5 : a 4 ≠ 7 := exclude [0,1,3,9] (edge r16) (a 4) (a 5) 7 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0,2] := remove (a 4) 7 [0,2,7] t4 b5
  have b6 : a 5 ≠ 3 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 3 t5 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0,1,9] := remove (a 5) 3 [0,1,3,9] d5 b6
  have b7 : a 5 ≠ 9 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 9 t5 c16 (by decide +kernel)
  have t7 : a 5 ∈ [0,1] := remove (a 5) 9 [0,1,9] t6 b7
  have b8 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r18 v u) (a 12) (a 4) 1 t5 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,2] := remove (a 12) 1 [0,1,2] d12 b8
  have b9 : a 12 ≠ 2 := exclude [0,2] (fun u v => edge r18 v u) (a 12) (a 4) 2 t5 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0] := remove (a 12) 2 [0,2] t8 b9
  have b10 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 3 t5 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b10
  have b11 : a 20 ≠ 7 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 7 t5 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,2,4,5,6,8,9,10,11] := remove (a 20) 7 [0,1,2,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 20 ≠ 9 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 9 t5 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,2,4,5,6,8,10,11] := remove (a 20) 9 [0,1,2,4,5,6,8,9,10,11] t11 b12
  have b13 : a 20 ≠ 11 := exclude [0,2] (fun u v => edge r19 v u) (a 20) (a 4) 11 t5 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,2,4,5,6,8,10] := remove (a 20) 11 [0,1,2,4,5,6,8,10,11] t12 b13
  have b14 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 2 t7 c20 (by decide +kernel)
  have t14 : a 7 ∈ [0,1,3,4,5] := remove (a 7) 2 [0,1,2,3,4,5] d7 b14
  have b15 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r20 v u) (a 7) (a 5) 4 t7 c20 (by decide +kernel)
  have t15 : a 7 ∈ [0,1,3,5] := remove (a 7) 4 [0,1,3,4,5] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t13 (t15))))))

theorem chunk3 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,2])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,1,2,4])
    (d9 : a 9 ∈ [0,1,3,5])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 21 ∈ [0] ∧ a 14 ∈ [0,1] ∧ a 22 ∈ [0,1,3,4,5,7,9,11] ∧ a 8 ∈ [0,1] ∧ a 9 ∈ [0,1,5] := by
  have b0 : a 21 ≠ 1 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b0
  have b1 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t0 b1
  have b2 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,4,5] := remove (a 21) 3 [0,3,4,5] t1 b2
  have b3 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,5] := remove (a 21) 4 [0,4,5] t2 b3
  have b4 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0] := remove (a 21) 5 [0,5] t3 b4
  have b5 : a 14 ≠ 2 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,3,4,5] := remove (a 14) 2 [0,1,2,3,4,5] d14 b5
  have b6 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,4,5] := remove (a 14) 3 [0,1,3,4,5] t5 b6
  have b7 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,5] := remove (a 14) 4 [0,1,4,5] t6 b7
  have b8 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,1] := remove (a 14) 5 [0,1,5] t7 b8
  have b9 : a 22 ≠ 2 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b9
  have b10 : a 22 ≠ 6 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,3,4,5,7,8,9,10,11] := remove (a 22) 6 [0,1,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 22 ≠ 8 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,3,4,5,7,9,10,11] := remove (a 22) 8 [0,1,3,4,5,7,8,9,10,11] t10 b11
  have b12 : a 22 ≠ 10 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,3,4,5,7,9,11] := remove (a 22) 10 [0,1,3,4,5,7,9,10,11] t11 b12
  have b13 : a 8 ≠ 2 := exclude [0,1,3,5] (edge r28) (a 8) (a 9) 2 d9 c28 (by decide +kernel)
  have t13 : a 8 ∈ [0,1,4] := remove (a 8) 2 [0,1,2,4] d8 b13
  have b14 : a 8 ≠ 4 := exclude [0,1,3,5] (edge r28) (a 8) (a 9) 4 d9 c28 (by decide +kernel)
  have t14 : a 8 ∈ [0,1] := remove (a 8) 4 [0,1,4] t13 b14
  have b15 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 3 t14 c28 (by decide +kernel)
  have t15 : a 9 ∈ [0,1,5] := remove (a 9) 3 [0,1,3,5] d9 b15
  exact And.intro t4 (And.intro t8 (And.intro t12 (And.intro t14 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_164
