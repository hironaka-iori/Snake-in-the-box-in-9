import PartitionData205_170
namespace PartitionCover205_170
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0])
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 22 ∈ [0,4,20,21,22,23] := by
  have b0 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d22 b0
  have b1 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 22 ≠ 7 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 22 ≠ 8 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,4,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 8 [0,4,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 22 ≠ 9 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,4,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 9 [0,4,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 22 ≠ 10 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,4,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 10 [0,4,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 22 ≠ 11 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,4,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 11 [0,4,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 22 ≠ 12 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 12 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,4,13,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 12 [0,4,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 22 ≠ 13 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 13 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,4,14,15,16,17,18,19,20,21,22,23] := remove (a 22) 13 [0,4,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 22 ≠ 14 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 14 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,4,15,16,17,18,19,20,21,22,23] := remove (a 22) 14 [0,4,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 22 ≠ 15 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 15 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,4,16,17,18,19,20,21,22,23] := remove (a 22) 15 [0,4,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 22 ≠ 16 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 16 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,4,17,18,19,20,21,22,23] := remove (a 22) 16 [0,4,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 22 ≠ 17 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 17 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,4,18,19,20,21,22,23] := remove (a 22) 17 [0,4,17,18,19,20,21,22,23] t12 b13
  have b14 : a 22 ≠ 18 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 18 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,4,19,20,21,22,23] := remove (a 22) 18 [0,4,18,19,20,21,22,23] t13 b14
  have b15 : a 22 ≠ 19 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 19 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,4,20,21,22,23] := remove (a 22) 19 [0,4,19,20,21,22,23] t14 b15
  exact t15

theorem chunk9 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,4,20,21,22,23])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d7 : a 7 ∈ [0])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 22 ∈ [0,4] ∧ a 15 ∈ [0,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 22 ≠ 20 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 20 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,4,21,22,23] := remove (a 22) 20 [0,4,20,21,22,23] d22 b0
  have b1 : a 22 ≠ 21 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 21 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,4,22,23] := remove (a 22) 21 [0,4,21,22,23] t0 b1
  have b2 : a 22 ≠ 22 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 22 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,4,23] := remove (a 22) 22 [0,4,22,23] t1 b2
  have b3 : a 22 ≠ 23 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 23 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,4] := remove (a 22) 23 [0,4,23] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d15 b4
  have b5 : a 15 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 15 ≠ 3 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 15 ≠ 4 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 15 ≠ 5 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 15 ≠ 6 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 15 ≠ 7 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 15 ≠ 8 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t11 : a 15 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 15 ≠ 9 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 15 ≠ 10 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 10 d7 c26 (by decide +kernel)
  have t13 : a 15 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 15 ≠ 11 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 11 d7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 15 ≠ 12 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 12 d7 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0,13,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 12 [0,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (t15)

theorem chunk10 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,13,14,15,16,17,18,19,20,21,22,23])
    (d7 : a 7 ∈ [0])
    (d9 : a 9 ∈ [0,1,4,5,6,7,10,11,12,13])
    (d8 : a 8 ∈ [0])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 15 ∈ [0,19] ∧ a 9 ∈ [0,1,12,13] := by
  have b0 : a 15 ≠ 13 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 13 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,14,15,16,17,18,19,20,21,22,23] := remove (a 15) 13 [0,13,14,15,16,17,18,19,20,21,22,23] d15 b0
  have b1 : a 15 ≠ 14 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 14 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,15,16,17,18,19,20,21,22,23] := remove (a 15) 14 [0,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 15 ≠ 15 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 15 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,16,17,18,19,20,21,22,23] := remove (a 15) 15 [0,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 15 ≠ 16 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 16 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,17,18,19,20,21,22,23] := remove (a 15) 16 [0,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 15 ≠ 17 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 17 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,18,19,20,21,22,23] := remove (a 15) 17 [0,17,18,19,20,21,22,23] t3 b4
  have b5 : a 15 ≠ 18 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 18 d7 c26 (by decide +kernel)
  have t5 : a 15 ∈ [0,19,20,21,22,23] := remove (a 15) 18 [0,18,19,20,21,22,23] t4 b5
  have b6 : a 15 ≠ 20 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 20 d7 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0,19,21,22,23] := remove (a 15) 20 [0,19,20,21,22,23] t5 b6
  have b7 : a 15 ≠ 21 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 21 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0,19,22,23] := remove (a 15) 21 [0,19,21,22,23] t6 b7
  have b8 : a 15 ≠ 22 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 22 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,19,23] := remove (a 15) 22 [0,19,22,23] t7 b8
  have b9 : a 15 ≠ 23 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 23 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,19] := remove (a 15) 23 [0,19,23] t8 b9
  have b10 : a 9 ≠ 4 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t10 : a 9 ∈ [0,1,5,6,7,10,11,12,13] := remove (a 9) 4 [0,1,4,5,6,7,10,11,12,13] d9 b10
  have b11 : a 9 ≠ 5 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t11 : a 9 ∈ [0,1,6,7,10,11,12,13] := remove (a 9) 5 [0,1,5,6,7,10,11,12,13] t10 b11
  have b12 : a 9 ≠ 6 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 6 d8 c28 (by decide +kernel)
  have t12 : a 9 ∈ [0,1,7,10,11,12,13] := remove (a 9) 6 [0,1,6,7,10,11,12,13] t11 b12
  have b13 : a 9 ≠ 7 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 7 d8 c28 (by decide +kernel)
  have t13 : a 9 ∈ [0,1,10,11,12,13] := remove (a 9) 7 [0,1,7,10,11,12,13] t12 b13
  have b14 : a 9 ≠ 10 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 10 d8 c28 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,11,12,13] := remove (a 9) 10 [0,1,10,11,12,13] t13 b14
  have b15 : a 9 ≠ 11 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 11 d8 c28 (by decide +kernel)
  have t15 : a 9 ∈ [0,1,12,13] := remove (a 9) 11 [0,1,11,12,13] t14 b15
  exact And.intro t9 (t15)

theorem chunk11 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,12,13])
    (d8 : a 8 ∈ [0])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 9 ∈ [0,1] ∧ a 10 ∈ [0] ∧ a 24 ∈ [0,3,5,6,7,8,9,10,11] := by
  have b0 : a 9 ≠ 12 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 12 d8 c28 (by decide +kernel)
  have t0 : a 9 ∈ [0,1,13] := remove (a 9) 12 [0,1,12,13] d9 b0
  have b1 : a 9 ≠ 13 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 13 d8 c28 (by decide +kernel)
  have t1 : a 9 ∈ [0,1] := remove (a 9) 13 [0,1,13] t0 b1
  have b2 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 d8 c29 (by decide +kernel)
  have t2 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b2
  have b3 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 10) 2 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 10 ≠ 3 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t4 : a 10 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 10) 3 [0,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 10 ≠ 4 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 4 d8 c29 (by decide +kernel)
  have t5 : a 10 ∈ [0,5,6,7,8,9,10,11] := remove (a 10) 4 [0,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 10 ≠ 5 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 5 d8 c29 (by decide +kernel)
  have t6 : a 10 ∈ [0,6,7,8,9,10,11] := remove (a 10) 5 [0,5,6,7,8,9,10,11] t5 b6
  have b7 : a 10 ≠ 6 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 6 d8 c29 (by decide +kernel)
  have t7 : a 10 ∈ [0,7,8,9,10,11] := remove (a 10) 6 [0,6,7,8,9,10,11] t6 b7
  have b8 : a 10 ≠ 7 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 7 d8 c29 (by decide +kernel)
  have t8 : a 10 ∈ [0,8,9,10,11] := remove (a 10) 7 [0,7,8,9,10,11] t7 b8
  have b9 : a 10 ≠ 8 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 8 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,9,10,11] := remove (a 10) 8 [0,8,9,10,11] t8 b9
  have b10 : a 10 ≠ 9 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 9 d8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,10,11] := remove (a 10) 9 [0,9,10,11] t9 b10
  have b11 : a 10 ≠ 10 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 10 d8 c29 (by decide +kernel)
  have t11 : a 10 ∈ [0,11] := remove (a 10) 10 [0,10,11] t10 b11
  have b12 : a 10 ≠ 11 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 11 d8 c29 (by decide +kernel)
  have t12 : a 10 ∈ [0] := remove (a 10) 11 [0,11] t11 b12
  have b13 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b13
  have b14 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 24) 4 [0,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t12 (t15))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_170
