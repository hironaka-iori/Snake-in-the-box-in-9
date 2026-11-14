import PartitionData205_181
namespace PartitionCover205_181
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,4,9,10,11,12,13,14,15,16,17])
    (d6 : a 6 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d7 : a 7 ∈ [0,3])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 14 ∈ [0,4] ∧ a 22 ∈ [0,1,2] ∧ a 15 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 14 ≠ 9 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,4,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,4,9,10,11,12,13,14,15,16,17] d14 b0
  have b1 : a 14 ≠ 10 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,4,11,12,13,14,15,16,17] := remove (a 14) 10 [0,4,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 14 ≠ 11 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,4,12,13,14,15,16,17] := remove (a 14) 11 [0,4,11,12,13,14,15,16,17] t1 b2
  have b3 : a 14 ≠ 12 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 12 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,4,13,14,15,16,17] := remove (a 14) 12 [0,4,12,13,14,15,16,17] t2 b3
  have b4 : a 14 ≠ 13 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 13 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,4,14,15,16,17] := remove (a 14) 13 [0,4,13,14,15,16,17] t3 b4
  have b5 : a 14 ≠ 14 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 14 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,4,15,16,17] := remove (a 14) 14 [0,4,14,15,16,17] t4 b5
  have b6 : a 14 ≠ 15 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,4,16,17] := remove (a 14) 15 [0,4,15,16,17] t5 b6
  have b7 : a 14 ≠ 16 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,4,17] := remove (a 14) 16 [0,4,16,17] t6 b7
  have b8 : a 14 ≠ 17 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,4] := remove (a 14) 17 [0,4,17] t7 b8
  have b9 : a 22 ≠ 3 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,2,4,5,6,7,8] := remove (a 22) 3 [0,1,2,3,4,5,6,7,8] d22 b9
  have b10 : a 22 ≠ 4 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,2,5,6,7,8] := remove (a 22) 4 [0,1,2,4,5,6,7,8] t9 b10
  have b11 : a 22 ≠ 5 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,2,6,7,8] := remove (a 22) 5 [0,1,2,5,6,7,8] t10 b11
  have b12 : a 22 ≠ 6 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,2,7,8] := remove (a 22) 6 [0,1,2,6,7,8] t11 b12
  have b13 : a 22 ≠ 7 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,2,8] := remove (a 22) 7 [0,1,2,7,8] t12 b13
  have b14 : a 22 ≠ 8 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,2] := remove (a 22) 8 [0,1,2,8] t13 b14
  have b15 : a 15 ≠ 4 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 15) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d15 b15
  exact And.intro t8 (And.intro t14 (t15))

theorem chunk5 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d7 : a 7 ∈ [0,3])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    : a 15 ∈ [0,1,2,3,12,13,14,15] ∧ a 23 ∈ [0,2,6,8,9,10,11] := by
  have b0 : a 15 ≠ 5 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 15) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d15 b0
  have b1 : a 15 ≠ 6 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 15) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 15 ≠ 7 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 15) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 15 ≠ 8 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19] := remove (a 15) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 15 ≠ 9 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19] := remove (a 15) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 15 ≠ 10 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 10 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19] := remove (a 15) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 15 ≠ 11 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 11 d7 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,2,3,12,13,14,15,16,17,18,19] := remove (a 15) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 15 ≠ 16 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 16 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,2,3,12,13,14,15,17,18,19] := remove (a 15) 16 [0,1,2,3,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 15 ≠ 17 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 17 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,2,3,12,13,14,15,18,19] := remove (a 15) 17 [0,1,2,3,12,13,14,15,17,18,19] t7 b8
  have b9 : a 15 ≠ 18 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 18 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,2,3,12,13,14,15,19] := remove (a 15) 18 [0,1,2,3,12,13,14,15,18,19] t8 b9
  have b10 : a 15 ≠ 19 := exclude [0,3] (fun u v => edge r26 v u) (a 15) (a 7) 19 d7 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,2,3,12,13,14,15] := remove (a 15) 19 [0,1,2,3,12,13,14,15,19] t9 b10
  have b11 : a 23 ≠ 1 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b11
  have b12 : a 23 ≠ 3 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,2,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 23 ≠ 4 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 23) 4 [0,2,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 23 ≠ 5 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0,2,6,7,8,9,10,11] := remove (a 23) 5 [0,2,5,6,7,8,9,10,11] t13 b14
  have b15 : a 23 ≠ 7 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t15 : a 23 ∈ [0,2,6,8,9,10,11] := remove (a 23) 7 [0,2,6,7,8,9,10,11] t14 b15
  exact And.intro t10 (t15)

theorem chunk6 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,2,6,8,9,10,11])
    (d7 : a 7 ∈ [0,3])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,6])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 23 ∈ [0,2,6,8] ∧ a 9 ∈ [0,3] ∧ a 10 ∈ [0,1] ∧ a 12 ∈ [0,2] ∧ a 24 ∈ [0,4,5,6,7,8,9,10,11] := by
  have b0 : a 23 ≠ 9 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,2,6,8,10,11] := remove (a 23) 9 [0,2,6,8,9,10,11] d23 b0
  have b1 : a 23 ≠ 10 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t1 : a 23 ∈ [0,2,6,8,11] := remove (a 23) 10 [0,2,6,8,10,11] t0 b1
  have b2 : a 23 ≠ 11 := exclude [0,3] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t2 : a 23 ∈ [0,2,6,8] := remove (a 23) 11 [0,2,6,8,11] t1 b2
  have b3 : a 9 ≠ 1 := exclude [0,6] (fun u v => edge r28 v u) (a 9) (a 8) 1 d8 c28 (by decide +kernel)
  have t3 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b3
  have b4 : a 9 ≠ 2 := exclude [0,6] (fun u v => edge r28 v u) (a 9) (a 8) 2 d8 c28 (by decide +kernel)
  have t4 : a 9 ∈ [0,3,4,5] := remove (a 9) 2 [0,2,3,4,5] t3 b4
  have b5 : a 9 ≠ 4 := exclude [0,6] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0,3,5] := remove (a 9) 4 [0,3,4,5] t4 b5
  have b6 : a 9 ≠ 5 := exclude [0,6] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t6 : a 9 ∈ [0,3] := remove (a 9) 5 [0,3,5] t5 b6
  have b7 : a 10 ≠ 2 := exclude [0,6] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,3,4,5] := remove (a 10) 2 [0,1,2,3,4,5] d10 b7
  have b8 : a 10 ≠ 3 := exclude [0,6] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,4,5] := remove (a 10) 3 [0,1,3,4,5] t7 b8
  have b9 : a 10 ≠ 4 := exclude [0,6] (fun u v => edge r29 v u) (a 10) (a 8) 4 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,5] := remove (a 10) 4 [0,1,4,5] t8 b9
  have b10 : a 10 ≠ 5 := exclude [0,6] (fun u v => edge r29 v u) (a 10) (a 8) 5 d8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,1] := remove (a 10) 5 [0,1,5] t9 b10
  have b11 : a 12 ≠ 1 := exclude [0,6] (fun u v => edge r30 v u) (a 12) (a 8) 1 d8 c30 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b11
  have b12 : a 12 ≠ 3 := exclude [0,6] (fun u v => edge r30 v u) (a 12) (a 8) 3 d8 c30 (by decide +kernel)
  have t12 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t11 b12
  have b13 : a 24 ≠ 1 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b13
  have b14 : a 24 ≠ 2 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 24 ≠ 3 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t10 (And.intro t12 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,4,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,6])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d9 : a 9 ∈ [0,3])
    (d11 : a 11 ∈ [0,1,6,7])
    (d10 : a 10 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1,2,3,12,13,14,15])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 24 ∈ [0,6] ∧ a 25 ∈ [0,2,3,4,7,8] ∧ a 11 ∈ [0,6] ∧ a 26 ∈ [0,1,3,4] ∧ a 15 ∈ [0,2,3,12,13,14,15] := by
  have b0 : a 24 ≠ 4 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,5,6,7,8,9,10,11] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11] d24 b0
  have b1 : a 24 ≠ 5 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,6,7,8,9,10,11] := remove (a 24) 5 [0,5,6,7,8,9,10,11] t0 b1
  have b2 : a 24 ≠ 7 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,6,8,9,10,11] := remove (a 24) 7 [0,6,7,8,9,10,11] t1 b2
  have b3 : a 24 ≠ 8 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,6,9,10,11] := remove (a 24) 8 [0,6,8,9,10,11] t2 b3
  have b4 : a 24 ≠ 9 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,6,10,11] := remove (a 24) 9 [0,6,9,10,11] t3 b4
  have b5 : a 24 ≠ 10 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,6,11] := remove (a 24) 10 [0,6,10,11] t4 b5
  have b6 : a 24 ≠ 11 := exclude [0,6] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,6] := remove (a 24) 11 [0,6,11] t5 b6
  have b7 : a 25 ≠ 1 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9] d25 b7
  have b8 : a 25 ≠ 5 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,3,4,6,7,8,9] := remove (a 25) 5 [0,2,3,4,5,6,7,8,9] t7 b8
  have b9 : a 25 ≠ 6 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,3,4,7,8,9] := remove (a 25) 6 [0,2,3,4,6,7,8,9] t8 b9
  have b10 : a 25 ≠ 9 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,2,3,4,7,8] := remove (a 25) 9 [0,2,3,4,7,8,9] t9 b10
  have b11 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r35 v u) (a 11) (a 10) 1 d10 c35 (by decide +kernel)
  have t11 : a 11 ∈ [0,6,7] := remove (a 11) 1 [0,1,6,7] d11 b11
  have b12 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r35 v u) (a 11) (a 10) 7 d10 c35 (by decide +kernel)
  have t12 : a 11 ∈ [0,6] := remove (a 11) 7 [0,6,7] t11 b12
  have b13 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,3,4,5] := remove (a 26) 2 [0,1,2,3,4,5] d26 b13
  have b14 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,3,4] := remove (a 26) 5 [0,1,3,4,5] t13 b14
  have b15 : a 15 ≠ 1 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 1 t12 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0,2,3,12,13,14,15] := remove (a 15) 1 [0,1,2,3,12,13,14,15] d15 b15
  exact And.intro t6 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_181
