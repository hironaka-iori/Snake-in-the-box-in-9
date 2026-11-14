import PartitionData205_169
namespace PartitionCover205_169
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,13])
    (d6 : a 6 ∈ [0,2,4,8])
    (d7 : a 7 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 21 ∈ [0,10,11] ∧ a 6 ∈ [0,2] ∧ a 14 ∈ [0,1] ∧ a 22 ∈ [0,1,4,5,6,7,8,9,10,11] := by
  have b0 : a 21 ≠ 2 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 21) 2 [0,2,3,4,5,6,7,8,9,10,11] d21 b0
  have b1 : a 21 ≠ 3 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 21) 3 [0,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 21 ≠ 4 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0,5,6,7,8,9,10,11] := remove (a 21) 4 [0,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 21 ≠ 5 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t3 : a 21 ∈ [0,6,7,8,9,10,11] := remove (a 21) 5 [0,5,6,7,8,9,10,11] t2 b3
  have b4 : a 21 ≠ 6 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 6 d5 c22 (by decide +kernel)
  have t4 : a 21 ∈ [0,7,8,9,10,11] := remove (a 21) 6 [0,6,7,8,9,10,11] t3 b4
  have b5 : a 21 ≠ 7 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,8,9,10,11] := remove (a 21) 7 [0,7,8,9,10,11] t4 b5
  have b6 : a 21 ≠ 8 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 8 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,9,10,11] := remove (a 21) 8 [0,8,9,10,11] t5 b6
  have b7 : a 21 ≠ 9 := exclude [0,13] (fun u v => edge r22 v u) (a 21) (a 5) 9 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,10,11] := remove (a 21) 9 [0,9,10,11] t6 b7
  have b8 : a 6 ≠ 4 := exclude [0,2] (edge r23) (a 6) (a 7) 4 d7 c23 (by decide +kernel)
  have t8 : a 6 ∈ [0,2,8] := remove (a 6) 4 [0,2,4,8] d6 b8
  have b9 : a 6 ≠ 8 := exclude [0,2] (edge r23) (a 6) (a 7) 8 d7 c23 (by decide +kernel)
  have t9 : a 6 ∈ [0,2] := remove (a 6) 8 [0,2,8] t8 b9
  have b10 : a 14 ≠ 2 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 2 t9 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,3,4,5] := remove (a 14) 2 [0,1,2,3,4,5] d14 b10
  have b11 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 t9 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,4,5] := remove (a 14) 3 [0,1,3,4,5] t10 b11
  have b12 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 t9 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,5] := remove (a 14) 4 [0,1,4,5] t11 b12
  have b13 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 t9 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0,1] := remove (a 14) 5 [0,1,5] t12 b13
  have b14 : a 22 ≠ 2 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 2 t9 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b14
  have b15 : a 22 ≠ 3 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 3 t9 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,1,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t7 (And.intro t9 (And.intro t13 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,1,4,5])
    (d9 : a 9 ∈ [0,5])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 22 ∈ [0,1,4,5] ∧ a 15 ∈ [0,2,3,5] ∧ a 23 ∈ [0,4,8,9,10,11] ∧ a 8 ∈ [0,5] := by
  have b0 : a 22 ≠ 6 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 22) 6 [0,1,4,5,6,7,8,9,10,11] d22 b0
  have b1 : a 22 ≠ 7 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,1,4,5,8,9,10,11] := remove (a 22) 7 [0,1,4,5,7,8,9,10,11] t0 b1
  have b2 : a 22 ≠ 8 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,1,4,5,9,10,11] := remove (a 22) 8 [0,1,4,5,8,9,10,11] t1 b2
  have b3 : a 22 ≠ 9 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,1,4,5,10,11] := remove (a 22) 9 [0,1,4,5,9,10,11] t2 b3
  have b4 : a 22 ≠ 10 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,4,5,11] := remove (a 22) 10 [0,1,4,5,10,11] t3 b4
  have b5 : a 22 ≠ 11 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,4,5] := remove (a 22) 11 [0,1,4,5,11] t4 b5
  have b6 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 1 d7 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0,2,3,4,5] := remove (a 15) 1 [0,1,2,3,4,5] d15 b6
  have b7 : a 15 ≠ 4 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0,2,3,5] := remove (a 15) 4 [0,2,3,4,5] t6 b7
  have b8 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b8
  have b9 : a 23 ≠ 2 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 23) 2 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 23 ≠ 5 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,4,6,7,8,9,10,11] := remove (a 23) 5 [0,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 23 ≠ 6 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,4,7,8,9,10,11] := remove (a 23) 6 [0,4,6,7,8,9,10,11] t11 b12
  have b13 : a 23 ≠ 7 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,4,8,9,10,11] := remove (a 23) 7 [0,4,7,8,9,10,11] t12 b13
  have b14 : a 8 ≠ 1 := exclude [0,5] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t14 : a 8 ∈ [0,4,5] := remove (a 8) 1 [0,1,4,5] d8 b14
  have b15 : a 8 ≠ 4 := exclude [0,5] (edge r28) (a 8) (a 9) 4 d9 c28 (by decide +kernel)
  have t15 : a 8 ∈ [0,5] := remove (a 8) 4 [0,4,5] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t13 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,5])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,5])
    (d25 : a 25 ∈ [0,1,2])
    (d14 : a 14 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 10 ∈ [0,5] ∧ a 11 ∈ [0,1,4,5] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0,1,4,5,12,13,14,15,16,17] := by
  have b0 : a 10 ≠ 2 := exclude [0,5] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,3,4,5] := remove (a 10) 2 [0,1,2,3,4,5] d10 b0
  have b1 : a 10 ≠ 3 := exclude [0,5] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,4,5] := remove (a 10) 3 [0,1,3,4,5] t0 b1
  have b2 : a 11 ≠ 2 := exclude [0,5] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t2 : a 11 ∈ [0,1,3,4,5] := remove (a 11) 2 [0,1,2,3,4,5] d11 b2
  have b3 : a 11 ≠ 3 := exclude [0,5] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t3 : a 11 ∈ [0,1,4,5] := remove (a 11) 3 [0,1,3,4,5] t2 b3
  have b4 : a 25 ≠ 1 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,2] := remove (a 25) 1 [0,1,2] d25 b4
  have b5 : a 25 ≠ 2 := exclude [0,5] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0] := remove (a 25) 2 [0,2] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,1] (edge r36) (a 10) (a 14) 1 d14 c36 (by decide +kernel)
  have t6 : a 10 ∈ [0,4,5] := remove (a 10) 1 [0,1,4,5] t1 b6
  have b7 : a 10 ≠ 4 := exclude [0,1] (edge r36) (a 10) (a 14) 4 d14 c36 (by decide +kernel)
  have t7 : a 10 ∈ [0,5] := remove (a 10) 4 [0,4,5] t6 b7
  have b8 : a 26 ≠ 2 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 2 t7 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d26 b8
  have b9 : a 26 ≠ 3 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 3 t7 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 26 ≠ 6 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 6 t7 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 26 ≠ 7 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 7 t7 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 26 ≠ 8 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 8 t7 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17] := remove (a 26) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 26 ≠ 9 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 9 t7 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,4,5,10,11,12,13,14,15,16,17] := remove (a 26) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 26 ≠ 10 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 10 t7 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,4,5,11,12,13,14,15,16,17] := remove (a 26) 10 [0,1,4,5,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 26 ≠ 11 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 11 t7 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,4,5,12,13,14,15,16,17] := remove (a 26) 11 [0,1,4,5,11,12,13,14,15,16,17] t14 b15
  exact And.intro t7 (And.intro t3 (And.intro t5 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,4,5,12,13,14,15,16,17])
    (d10 : a 10 ∈ [0,5])
    (d11 : a 11 ∈ [0,1,4,5])
    (d15 : a 15 ∈ [0,2,3,5])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 26 ∈ [0,1,4,5] ∧ a 11 ∈ [0,5] ∧ a 15 ∈ [0,5] ∧ a 27 ∈ [0,1,2,5] ∧ a 28 ∈ [0,1] := by
  have b0 : a 26 ≠ 12 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 12 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,4,5,13,14,15,16,17] := remove (a 26) 12 [0,1,4,5,12,13,14,15,16,17] d26 b0
  have b1 : a 26 ≠ 13 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 13 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,4,5,14,15,16,17] := remove (a 26) 13 [0,1,4,5,13,14,15,16,17] t0 b1
  have b2 : a 26 ≠ 14 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 14 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,4,5,15,16,17] := remove (a 26) 14 [0,1,4,5,14,15,16,17] t1 b2
  have b3 : a 26 ≠ 15 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 15 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,4,5,16,17] := remove (a 26) 15 [0,1,4,5,15,16,17] t2 b3
  have b4 : a 26 ≠ 16 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 16 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,4,5,17] := remove (a 26) 16 [0,1,4,5,16,17] t3 b4
  have b5 : a 26 ≠ 17 := exclude [0,5] (fun u v => edge r37 v u) (a 26) (a 10) 17 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,4,5] := remove (a 26) 17 [0,1,4,5,17] t4 b5
  have b6 : a 11 ≠ 1 := exclude [0,2,3,5] (edge r38) (a 11) (a 15) 1 d15 c38 (by decide +kernel)
  have t6 : a 11 ∈ [0,4,5] := remove (a 11) 1 [0,1,4,5] d11 b6
  have b7 : a 11 ≠ 4 := exclude [0,2,3,5] (edge r38) (a 11) (a 15) 4 d15 c38 (by decide +kernel)
  have t7 : a 11 ∈ [0,5] := remove (a 11) 4 [0,4,5] t6 b7
  have b8 : a 15 ≠ 2 := exclude [0,5] (fun u v => edge r38 v u) (a 15) (a 11) 2 t7 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0,3,5] := remove (a 15) 2 [0,2,3,5] d15 b8
  have b9 : a 15 ≠ 3 := exclude [0,5] (fun u v => edge r38 v u) (a 15) (a 11) 3 t7 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0,5] := remove (a 15) 3 [0,3,5] t8 b9
  have b10 : a 27 ≠ 3 := exclude [0,5] (fun u v => edge r39 v u) (a 27) (a 11) 3 t7 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,2,4,5] := remove (a 27) 3 [0,1,2,3,4,5] d27 b10
  have b11 : a 27 ≠ 4 := exclude [0,5] (fun u v => edge r39 v u) (a 27) (a 11) 4 t7 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,2,5] := remove (a 27) 4 [0,1,2,4,5] t10 b11
  have b12 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,1,3,4,5] := remove (a 28) 2 [0,1,2,3,4,5] d28 b12
  have b13 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,1,4,5] := remove (a 28) 3 [0,1,3,4,5] t12 b13
  have b14 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,1,5] := remove (a 28) 4 [0,1,4,5] t13 b14
  have b15 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,1] := remove (a 28) 5 [0,1,5] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_169
