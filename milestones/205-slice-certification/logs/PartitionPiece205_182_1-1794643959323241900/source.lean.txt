import PartitionData205_182
namespace PartitionCover205_182
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,7,8])
    (d2 : a 2 ∈ [0,1])
    (d7 : a 7 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d4 : a 4 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 18 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0,1,2,3] ∧ a 4 ∈ [0,1] ∧ a 20 ∈ [0,1,2,3,5,6,8] := by
  have b0 : a 18 ≠ 7 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,8] := remove (a 18) 7 [0,7,8] d18 b0
  have b1 : a 18 ≠ 8 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0] := remove (a 18) 8 [0,8] t0 b1
  have b2 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 1 d3 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b2
  have b3 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 2 [0,2] t2 b3
  have b4 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 11) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b4
  have b5 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 11) 5 [0,1,2,3,5,6,7,8,9,10,11] t4 b5
  have b6 : a 11 ≠ 6 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 11) 6 [0,1,2,3,6,7,8,9,10,11] t5 b6
  have b7 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,1,2,3,8,9,10,11] := remove (a 11) 7 [0,1,2,3,7,8,9,10,11] t6 b7
  have b8 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,2,3,9,10,11] := remove (a 11) 8 [0,1,2,3,8,9,10,11] t7 b8
  have b9 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,2,3,10,11] := remove (a 11) 9 [0,1,2,3,9,10,11] t8 b9
  have b10 : a 11 ≠ 10 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,1,2,3,11] := remove (a 11) 10 [0,1,2,3,10,11] t9 b10
  have b11 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,1,2,3] := remove (a 11) 11 [0,1,2,3,11] t10 b11
  have b12 : a 4 ≠ 2 := exclude [0,1] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t12 : a 4 ∈ [0,1,3] := remove (a 4) 2 [0,1,2,3] d4 b12
  have b13 : a 4 ≠ 3 := exclude [0,1] (edge r16) (a 4) (a 5) 3 d5 c16 (by decide +kernel)
  have t13 : a 4 ∈ [0,1] := remove (a 4) 3 [0,1,3] t12 b13
  have b14 : a 20 ≠ 4 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 4 t13 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,2,3,5,6,7,8] := remove (a 20) 4 [0,1,2,3,4,5,6,7,8] d20 b14
  have b15 : a 20 ≠ 7 := exclude [0,1] (fun u v => edge r19 v u) (a 20) (a 4) 7 t13 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,2,3,5,6,8] := remove (a 20) 7 [0,1,2,3,5,6,7,8] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t11 (And.intro t13 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (d6 : a 6 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 13 ∈ [0,1,2,3,4,5] ∧ a 21 ∈ [0] ∧ a 6 ∈ [0,2] ∧ a 14 ∈ [0,4,5] := by
  have b0 : a 13 ≠ 6 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,2,3,4,5,7,8] := remove (a 13) 6 [0,1,2,3,4,5,6,7,8] d13 b0
  have b1 : a 13 ≠ 7 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,2,3,4,5,8] := remove (a 13) 7 [0,1,2,3,4,5,7,8] t0 b1
  have b2 : a 13 ≠ 8 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,2,3,4,5] := remove (a 13) 8 [0,1,2,3,4,5,8] t1 b2
  have b3 : a 21 ≠ 1 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,2,3,4,5,6,7,8] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8] d21 b3
  have b4 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,3,4,5,6,7,8] := remove (a 21) 2 [0,2,3,4,5,6,7,8] t3 b4
  have b5 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,4,5,6,7,8] := remove (a 21) 3 [0,3,4,5,6,7,8] t4 b5
  have b6 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,5,6,7,8] := remove (a 21) 4 [0,4,5,6,7,8] t5 b6
  have b7 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,6,7,8] := remove (a 21) 5 [0,5,6,7,8] t6 b7
  have b8 : a 21 ≠ 6 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 6 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,7,8] := remove (a 21) 6 [0,6,7,8] t7 b8
  have b9 : a 21 ≠ 7 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0,8] := remove (a 21) 7 [0,7,8] t8 b9
  have b10 : a 21 ≠ 8 := exclude [0,1] (fun u v => edge r22 v u) (a 21) (a 5) 8 d5 c22 (by decide +kernel)
  have t10 : a 21 ∈ [0] := remove (a 21) 8 [0,8] t9 b10
  have b11 : a 6 ≠ 1 := exclude [0] (edge r23) (a 6) (a 7) 1 d7 c23 (by decide +kernel)
  have t11 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b11
  have b12 : a 6 ≠ 3 := exclude [0] (edge r23) (a 6) (a 7) 3 d7 c23 (by decide +kernel)
  have t12 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t11 b12
  have b13 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 1 t12 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b13
  have b14 : a 14 ≠ 2 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 2 t12 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,3,4,5] := remove (a 14) 2 [0,2,3,4,5] t13 b14
  have b15 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 t12 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,4,5] := remove (a 14) 3 [0,3,4,5] t14 b15
  exact And.intro t2 (And.intro t10 (And.intro t12 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,4,5])
    (d6 : a 6 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 14 ∈ [0] ∧ a 15 ∈ [0,1] ∧ a 23 ∈ [0,1] := by
  have b0 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,5] := remove (a 14) 4 [0,4,5] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0] := remove (a 14) 5 [0,5] t0 b1
  have b2 : a 15 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,3,4,5] := remove (a 15) 2 [0,1,2,3,4,5] d15 b2
  have b3 : a 15 ≠ 3 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,4,5] := remove (a 15) 3 [0,1,3,4,5] t2 b3
  have b4 : a 15 ≠ 4 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,5] := remove (a 15) 4 [0,1,4,5] t3 b4
  have b5 : a 15 ≠ 5 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1] := remove (a 15) 5 [0,1,5] t4 b5
  have b6 : a 23 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 23) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b6
  have b7 : a 23 ≠ 3 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,1,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 23 ≠ 4 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 23) 4 [0,1,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 23 ≠ 5 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,6,7,8,9,10,11] := remove (a 23) 5 [0,1,5,6,7,8,9,10,11] t8 b9
  have b10 : a 23 ≠ 6 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,7,8,9,10,11] := remove (a 23) 6 [0,1,6,7,8,9,10,11] t9 b10
  have b11 : a 23 ≠ 7 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,8,9,10,11] := remove (a 23) 7 [0,1,7,8,9,10,11] t10 b11
  have b12 : a 23 ≠ 8 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,9,10,11] := remove (a 23) 8 [0,1,8,9,10,11] t11 b12
  have b13 : a 23 ≠ 9 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,10,11] := remove (a 23) 9 [0,1,9,10,11] t12 b13
  have b14 : a 23 ≠ 10 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,11] := remove (a 23) 10 [0,1,10,11] t13 b14
  have b15 : a 23 ≠ 11 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1] := remove (a 23) 11 [0,1,11] t14 b15
  exact And.intro t1 (And.intro t5 (t15))

theorem chunk7 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,6])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d9 : a 9 ∈ [0,1,2])
    (d11 : a 11 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    : a 10 ∈ [0,2] ∧ a 24 ∈ [0,1,4] ∧ a 9 ∈ [0] ∧ a 11 ∈ [0,2] ∧ a 13 ∈ [0,2,3,4,5] := by
  have b0 : a 10 ≠ 1 := exclude [0,6] (fun u v => edge r29 v u) (a 10) (a 8) 1 d8 c29 (by decide +kernel)
  have t0 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b0
  have b1 : a 10 ≠ 3 := exclude [0,6] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t1 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t0 b1
  have b2 : a 24 ≠ 2 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b2
  have b3 : a 24 ≠ 3 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 24 ≠ 5 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,4,6,7,8,9,10,11] := remove (a 24) 5 [0,1,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 24 ≠ 6 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,4,7,8,9,10,11] := remove (a 24) 6 [0,1,4,6,7,8,9,10,11] t4 b5
  have b6 : a 24 ≠ 7 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,4,8,9,10,11] := remove (a 24) 7 [0,1,4,7,8,9,10,11] t5 b6
  have b7 : a 24 ≠ 8 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,4,9,10,11] := remove (a 24) 8 [0,1,4,8,9,10,11] t6 b7
  have b8 : a 24 ≠ 9 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,4,10,11] := remove (a 24) 9 [0,1,4,9,10,11] t7 b8
  have b9 : a 24 ≠ 10 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,4,11] := remove (a 24) 10 [0,1,4,10,11] t8 b9
  have b10 : a 24 ≠ 11 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,4] := remove (a 24) 11 [0,1,4,11] t9 b10
  have b11 : a 9 ≠ 1 := exclude [0,1,2,3] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t11 : a 9 ∈ [0,2] := remove (a 9) 1 [0,1,2] d9 b11
  have b12 : a 9 ≠ 2 := exclude [0,1,2,3] (edge r32) (a 9) (a 11) 2 d11 c32 (by decide +kernel)
  have t12 : a 9 ∈ [0] := remove (a 9) 2 [0,2] t11 b12
  have b13 : a 11 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 1 t12 c32 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b13
  have b14 : a 11 ≠ 3 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 3 t12 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0,2] := remove (a 11) 3 [0,2,3] t13 b14
  have b15 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 t12 c33 (by decide +kernel)
  have t15 : a 13 ∈ [0,2,3,4,5] := remove (a 13) 1 [0,1,2,3,4,5] d13 b15
  exact And.intro t1 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_182
