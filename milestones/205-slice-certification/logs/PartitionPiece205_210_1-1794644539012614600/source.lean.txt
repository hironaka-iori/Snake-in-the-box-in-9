import PartitionData205_210
namespace PartitionCover205_210
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,2,3])
    (d5 : a 5 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,1,4,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 21 ∈ [0,2] ∧ a 14 ∈ [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22] ∧ a 22 ∈ [0,1,2,3,4,5,7,9,10,11] ∧ a 15 ∈ [0,1,4,7] ∧ a 23 ∈ [0,1,4,5] := by
  have b0 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] d21 b0
  have b1 : a 14 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 5 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d14 b1
  have b2 : a 14 ≠ 9 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,2,3,4,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 9 [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 14 ≠ 15 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,19,20,21,22,23] := remove (a 14) 15 [0,1,2,3,4,6,7,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 14 ≠ 19 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 19 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,21,22,23] := remove (a 14) 19 [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 14 ≠ 21 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 21 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22,23] := remove (a 14) 21 [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,21,22,23] t4 b5
  have b6 : a 14 ≠ 23 := exclude [0,1,4,5] (fun u v => edge r24 v u) (a 14) (a 6) 23 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22] := remove (a 14) 23 [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22,23] t5 b6
  have b7 : a 22 ≠ 6 := exclude [0,1,4,5] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,1,2,3,4,5,7,8,9,10,11] := remove (a 22) 6 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b7
  have b8 : a 22 ≠ 8 := exclude [0,1,4,5] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,2,3,4,5,7,9,10,11] := remove (a 22) 8 [0,1,2,3,4,5,7,8,9,10,11] t7 b8
  have b9 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,3,4,5,6,7,8] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8] d15 b9
  have b10 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,4,5,6,7,8] := remove (a 15) 3 [0,1,3,4,5,6,7,8] t9 b10
  have b11 : a 15 ≠ 5 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t11 : a 15 ∈ [0,1,4,6,7,8] := remove (a 15) 5 [0,1,4,5,6,7,8] t10 b11
  have b12 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,4,7,8] := remove (a 15) 6 [0,1,4,6,7,8] t11 b12
  have b13 : a 15 ≠ 8 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,4,7] := remove (a 15) 8 [0,1,4,7,8] t12 b13
  have b14 : a 23 ≠ 2 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] d23 b14
  have b15 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,4,5] := remove (a 23) 3 [0,1,3,4,5] t14 b15
  exact And.intro t0 (And.intro t6 (And.intro t8 (And.intro t13 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,4,5,12,13,16,17])
    (d8 : a 8 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 12 ∈ [0,12] ∧ a 24 ∈ [0,8] := by
  have b0 : a 12 ≠ 1 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 1 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0,4,5,12,13,16,17] := remove (a 12) 1 [0,1,4,5,12,13,16,17] d12 b0
  have b1 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 4 d8 c30 (by decide +kernel)
  have t1 : a 12 ∈ [0,5,12,13,16,17] := remove (a 12) 4 [0,4,5,12,13,16,17] t0 b1
  have b2 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 5 d8 c30 (by decide +kernel)
  have t2 : a 12 ∈ [0,12,13,16,17] := remove (a 12) 5 [0,5,12,13,16,17] t1 b2
  have b3 : a 12 ≠ 13 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 13 d8 c30 (by decide +kernel)
  have t3 : a 12 ∈ [0,12,16,17] := remove (a 12) 13 [0,12,13,16,17] t2 b3
  have b4 : a 12 ≠ 16 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 16 d8 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0,12,17] := remove (a 12) 16 [0,12,16,17] t3 b4
  have b5 : a 12 ≠ 17 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 17 d8 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0,12] := remove (a 12) 17 [0,12,17] t4 b5
  have b6 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b6
  have b7 : a 24 ≠ 2 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,5,6,7,8,9,10,11] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,6,7,8,9,10,11] := remove (a 24) 5 [0,5,6,7,8,9,10,11] t9 b10
  have b11 : a 24 ≠ 6 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,7,8,9,10,11] := remove (a 24) 6 [0,6,7,8,9,10,11] t10 b11
  have b12 : a 24 ≠ 7 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,8,9,10,11] := remove (a 24) 7 [0,7,8,9,10,11] t11 b12
  have b13 : a 24 ≠ 9 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,8,10,11] := remove (a 24) 9 [0,8,9,10,11] t12 b13
  have b14 : a 24 ≠ 10 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,8,11] := remove (a 24) 10 [0,8,10,11] t13 b14
  have b15 : a 24 ≠ 11 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,8] := remove (a 24) 11 [0,8,11] t14 b15
  exact And.intro t5 (t15)

theorem chunk6 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 10 ∈ [0,2] ∧ a 11 ∈ [0,2] ∧ a 14 ∈ [0,1,10,11,12,13,14,16,17,18] ∧ a 26 ∈ [0,2,3,5,8,9,10,11] := by
  have b0 : a 10 ≠ 1 := exclude [0,1,2,3] (edge r35) (a 10) (a 11) 1 d11 c35 (by decide +kernel)
  have t0 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b0
  have b1 : a 10 ≠ 3 := exclude [0,1,2,3] (edge r35) (a 10) (a 11) 3 d11 c35 (by decide +kernel)
  have t1 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t0 b1
  have b2 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r35 v u) (a 11) (a 10) 1 t1 c35 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b2
  have b3 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r35 v u) (a 11) (a 10) 3 t1 c35 (by decide +kernel)
  have t3 : a 11 ∈ [0,2] := remove (a 11) 3 [0,2,3] t2 b3
  have b4 : a 14 ≠ 2 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 2 t1 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22] := remove (a 14) 2 [0,1,2,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22] d14 b4
  have b5 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 3 t1 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,4,6,7,8,10,11,12,13,14,16,17,18,20,22] := remove (a 14) 3 [0,1,3,4,6,7,8,10,11,12,13,14,16,17,18,20,22] t4 b5
  have b6 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 4 t1 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,6,7,8,10,11,12,13,14,16,17,18,20,22] := remove (a 14) 4 [0,1,4,6,7,8,10,11,12,13,14,16,17,18,20,22] t5 b6
  have b7 : a 14 ≠ 6 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 6 t1 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,7,8,10,11,12,13,14,16,17,18,20,22] := remove (a 14) 6 [0,1,6,7,8,10,11,12,13,14,16,17,18,20,22] t6 b7
  have b8 : a 14 ≠ 7 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 7 t1 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,8,10,11,12,13,14,16,17,18,20,22] := remove (a 14) 7 [0,1,7,8,10,11,12,13,14,16,17,18,20,22] t7 b8
  have b9 : a 14 ≠ 8 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 8 t1 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,10,11,12,13,14,16,17,18,20,22] := remove (a 14) 8 [0,1,8,10,11,12,13,14,16,17,18,20,22] t8 b9
  have b10 : a 14 ≠ 20 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 20 t1 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,10,11,12,13,14,16,17,18,22] := remove (a 14) 20 [0,1,10,11,12,13,14,16,17,18,20,22] t9 b10
  have b11 : a 14 ≠ 22 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 22 t1 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,10,11,12,13,14,16,17,18] := remove (a 14) 22 [0,1,10,11,12,13,14,16,17,18,22] t10 b11
  have b12 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 1 t1 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b12
  have b13 : a 26 ≠ 4 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 4 t1 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 26) 4 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 26 ≠ 6 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 6 t1 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,2,3,5,7,8,9,10,11] := remove (a 26) 6 [0,2,3,5,6,7,8,9,10,11] t13 b14
  have b15 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 t1 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,2,3,5,8,9,10,11] := remove (a 26) 7 [0,2,3,5,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t11 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,2,3,5,8,9,10,11])
    (d10 : a 10 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,4,7])
    (d11 : a 11 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,12])
    (d14 : a 14 ∈ [0,1,10,11,12,13,14,16,17,18])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 26 ∈ [0,2,3,5,8,11] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,1,4] ∧ a 13 ∈ [0,1] ∧ a 14 ∈ [0,1,12,13] ∧ a 28 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 26 ≠ 9 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,2,3,5,8,10,11] := remove (a 26) 9 [0,2,3,5,8,9,10,11] d26 b0
  have b1 : a 26 ≠ 10 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,2,3,5,8,11] := remove (a 26) 10 [0,2,3,5,8,10,11] t0 b1
  have b2 : a 15 ≠ 4 := exclude [0,2] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,7] := remove (a 15) 4 [0,1,4,7] d15 b2
  have b3 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r38 v u) (a 15) (a 11) 7 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,1] := remove (a 15) 7 [0,1,7] t2 b3
  have b4 : a 27 ≠ 2 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,3,4,5] := remove (a 27) 2 [0,1,2,3,4,5] d27 b4
  have b5 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,4,5] := remove (a 27) 3 [0,1,3,4,5] t4 b5
  have b6 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,4] := remove (a 27) 5 [0,1,4,5] t5 b6
  have b7 : a 13 ≠ 2 := exclude [0,12] (fun u v => edge r40 v u) (a 13) (a 12) 2 d12 c40 (by decide +kernel)
  have t7 : a 13 ∈ [0,1] := remove (a 13) 2 [0,1,2] d13 b7
  have b8 : a 14 ≠ 10 := exclude [0,12] (fun u v => edge r41 v u) (a 14) (a 12) 10 d12 c41 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,11,12,13,14,16,17,18] := remove (a 14) 10 [0,1,10,11,12,13,14,16,17,18] d14 b8
  have b9 : a 14 ≠ 11 := exclude [0,12] (fun u v => edge r41 v u) (a 14) (a 12) 11 d12 c41 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,12,13,14,16,17,18] := remove (a 14) 11 [0,1,11,12,13,14,16,17,18] t8 b9
  have b10 : a 14 ≠ 14 := exclude [0,12] (fun u v => edge r41 v u) (a 14) (a 12) 14 d12 c41 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,12,13,16,17,18] := remove (a 14) 14 [0,1,12,13,14,16,17,18] t9 b10
  have b11 : a 14 ≠ 16 := exclude [0,12] (fun u v => edge r41 v u) (a 14) (a 12) 16 d12 c41 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,12,13,17,18] := remove (a 14) 16 [0,1,12,13,16,17,18] t10 b11
  have b12 : a 14 ≠ 17 := exclude [0,12] (fun u v => edge r41 v u) (a 14) (a 12) 17 d12 c41 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,12,13,18] := remove (a 14) 17 [0,1,12,13,17,18] t11 b12
  have b13 : a 14 ≠ 18 := exclude [0,12] (fun u v => edge r41 v u) (a 14) (a 12) 18 d12 c41 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,12,13] := remove (a 14) 18 [0,1,12,13,18] t12 b13
  have b14 : a 28 ≠ 1 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b14
  have b15 : a 28 ≠ 2 := exclude [0,12] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t6 (And.intro t7 (And.intro t13 (t15)))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_210
