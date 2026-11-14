import PartitionData205_215
namespace PartitionCover205_215
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,8,9,10,11])
    (d5 : a 5 ∈ [0,18])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21])
    (d6 : a 6 ∈ [0])
    (c18 : edge r18 (a 5) (a 19)=true)
    (c19 : edge r19 (a 6) (a 14)=true)
    : a 19 ∈ [0,9] ∧ a 14 ∈ [0,3,4,7,17,18,19,20,21] := by
  have b0 : a 19 ≠ 8 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 8 d5 c18 (by decide +kernel)
  have t0 : a 19 ∈ [0,9,10,11] := remove (a 19) 8 [0,8,9,10,11] d19 b0
  have b1 : a 19 ≠ 10 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 10 d5 c18 (by decide +kernel)
  have t1 : a 19 ∈ [0,9,11] := remove (a 19) 10 [0,9,10,11] t0 b1
  have b2 : a 19 ≠ 11 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 11 d5 c18 (by decide +kernel)
  have t2 : a 19 ∈ [0,9] := remove (a 19) 11 [0,9,11] t1 b2
  have b3 : a 14 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 1 d6 c19 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] d14 b3
  have b4 : a 14 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 2 d6 c19 (by decide +kernel)
  have t4 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t3 b4
  have b5 : a 14 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 5 d6 c19 (by decide +kernel)
  have t5 : a 14 ∈ [0,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 5 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t4 b5
  have b6 : a 14 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 6 d6 c19 (by decide +kernel)
  have t6 : a 14 ∈ [0,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 6 [0,3,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t5 b6
  have b7 : a 14 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 8 d6 c19 (by decide +kernel)
  have t7 : a 14 ∈ [0,3,4,7,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 8 [0,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t6 b7
  have b8 : a 14 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 9 d6 c19 (by decide +kernel)
  have t8 : a 14 ∈ [0,3,4,7,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 9 [0,3,4,7,9,10,11,12,13,14,15,16,17,18,19,20,21] t7 b8
  have b9 : a 14 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 10 d6 c19 (by decide +kernel)
  have t9 : a 14 ∈ [0,3,4,7,11,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 10 [0,3,4,7,10,11,12,13,14,15,16,17,18,19,20,21] t8 b9
  have b10 : a 14 ≠ 11 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 11 d6 c19 (by decide +kernel)
  have t10 : a 14 ∈ [0,3,4,7,12,13,14,15,16,17,18,19,20,21] := remove (a 14) 11 [0,3,4,7,11,12,13,14,15,16,17,18,19,20,21] t9 b10
  have b11 : a 14 ≠ 12 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 12 d6 c19 (by decide +kernel)
  have t11 : a 14 ∈ [0,3,4,7,13,14,15,16,17,18,19,20,21] := remove (a 14) 12 [0,3,4,7,12,13,14,15,16,17,18,19,20,21] t10 b11
  have b12 : a 14 ≠ 13 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 13 d6 c19 (by decide +kernel)
  have t12 : a 14 ∈ [0,3,4,7,14,15,16,17,18,19,20,21] := remove (a 14) 13 [0,3,4,7,13,14,15,16,17,18,19,20,21] t11 b12
  have b13 : a 14 ≠ 14 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 14 d6 c19 (by decide +kernel)
  have t13 : a 14 ∈ [0,3,4,7,15,16,17,18,19,20,21] := remove (a 14) 14 [0,3,4,7,14,15,16,17,18,19,20,21] t12 b13
  have b14 : a 14 ≠ 15 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 15 d6 c19 (by decide +kernel)
  have t14 : a 14 ∈ [0,3,4,7,16,17,18,19,20,21] := remove (a 14) 15 [0,3,4,7,15,16,17,18,19,20,21] t13 b14
  have b15 : a 14 ≠ 16 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 16 d6 c19 (by decide +kernel)
  have t15 : a 14 ∈ [0,3,4,7,17,18,19,20,21] := remove (a 14) 16 [0,3,4,7,16,17,18,19,20,21] t14 b15
  exact And.intro t2 (t15)

theorem chunk5 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,3,4,7,17,18,19,20,21])
    (d6 : a 6 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c19 : edge r19 (a 6) (a 14)=true)
    (c20 : edge r20 (a 6) (a 20)=true)
    : a 14 ∈ [0,3,4,7,18,21] ∧ a 20 ∈ [0,3,12,15,17,18,19,20,21,22,23] := by
  have b0 : a 14 ≠ 17 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 17 d6 c19 (by decide +kernel)
  have t0 : a 14 ∈ [0,3,4,7,18,19,20,21] := remove (a 14) 17 [0,3,4,7,17,18,19,20,21] d14 b0
  have b1 : a 14 ≠ 19 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 19 d6 c19 (by decide +kernel)
  have t1 : a 14 ∈ [0,3,4,7,18,20,21] := remove (a 14) 19 [0,3,4,7,18,19,20,21] t0 b1
  have b2 : a 14 ≠ 20 := exclude [0] (fun u v => edge r19 v u) (a 14) (a 6) 20 d6 c19 (by decide +kernel)
  have t2 : a 14 ∈ [0,3,4,7,18,21] := remove (a 14) 20 [0,3,4,7,18,20,21] t1 b2
  have b3 : a 20 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 1 d6 c20 (by decide +kernel)
  have t3 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d20 b3
  have b4 : a 20 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 2 d6 c20 (by decide +kernel)
  have t4 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 20 ≠ 4 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 4 d6 c20 (by decide +kernel)
  have t5 : a 20 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 20 ≠ 5 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 5 d6 c20 (by decide +kernel)
  have t6 : a 20 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 20 ≠ 6 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 6 d6 c20 (by decide +kernel)
  have t7 : a 20 ∈ [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 6 [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 20 ≠ 7 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 7 d6 c20 (by decide +kernel)
  have t8 : a 20 ∈ [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 7 [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 20 ≠ 8 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 8 d6 c20 (by decide +kernel)
  have t9 : a 20 ∈ [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 8 [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 20 ≠ 9 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 9 d6 c20 (by decide +kernel)
  have t10 : a 20 ∈ [0,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 9 [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 20 ≠ 10 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 10 d6 c20 (by decide +kernel)
  have t11 : a 20 ∈ [0,3,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 10 [0,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 20 ≠ 11 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 11 d6 c20 (by decide +kernel)
  have t12 : a 20 ∈ [0,3,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 11 [0,3,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 20 ≠ 13 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 13 d6 c20 (by decide +kernel)
  have t13 : a 20 ∈ [0,3,12,14,15,16,17,18,19,20,21,22,23] := remove (a 20) 13 [0,3,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 20 ≠ 14 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 14 d6 c20 (by decide +kernel)
  have t14 : a 20 ∈ [0,3,12,15,16,17,18,19,20,21,22,23] := remove (a 20) 14 [0,3,12,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 20 ≠ 16 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 16 d6 c20 (by decide +kernel)
  have t15 : a 20 ∈ [0,3,12,15,17,18,19,20,21,22,23] := remove (a 20) 16 [0,3,12,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t2 (t15)

theorem chunk6 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,3,12,15,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0])
    (d7 : a 7 ∈ [0,1,2])
    (d8 : a 8 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c20 : edge r20 (a 6) (a 20)=true)
    (c21 : edge r21 (a 7) (a 8)=true)
    (c22 : edge r22 (a 7) (a 9)=true)
    (c24 : edge r24 (a 7) (a 21)=true)
    : a 20 ∈ [0,3,12,15,20,22] ∧ a 7 ∈ [0,2] ∧ a 8 ∈ [0,3] ∧ a 9 ∈ [0,1,2,3,8,9,10,11] ∧ a 21 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 20 ≠ 17 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 17 d6 c20 (by decide +kernel)
  have t0 : a 20 ∈ [0,3,12,15,18,19,20,21,22,23] := remove (a 20) 17 [0,3,12,15,17,18,19,20,21,22,23] d20 b0
  have b1 : a 20 ≠ 18 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 18 d6 c20 (by decide +kernel)
  have t1 : a 20 ∈ [0,3,12,15,19,20,21,22,23] := remove (a 20) 18 [0,3,12,15,18,19,20,21,22,23] t0 b1
  have b2 : a 20 ≠ 19 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 19 d6 c20 (by decide +kernel)
  have t2 : a 20 ∈ [0,3,12,15,20,21,22,23] := remove (a 20) 19 [0,3,12,15,19,20,21,22,23] t1 b2
  have b3 : a 20 ≠ 21 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 21 d6 c20 (by decide +kernel)
  have t3 : a 20 ∈ [0,3,12,15,20,22,23] := remove (a 20) 21 [0,3,12,15,20,21,22,23] t2 b3
  have b4 : a 20 ≠ 23 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 23 d6 c20 (by decide +kernel)
  have t4 : a 20 ∈ [0,3,12,15,20,22] := remove (a 20) 23 [0,3,12,15,20,22,23] t3 b4
  have b5 : a 7 ≠ 1 := exclude [0,1,2,3] (edge r21) (a 7) (a 8) 1 d8 c21 (by decide +kernel)
  have t5 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b5
  have b6 : a 8 ≠ 1 := exclude [0,2] (fun u v => edge r21 v u) (a 8) (a 7) 1 t5 c21 (by decide +kernel)
  have t6 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b6
  have b7 : a 8 ≠ 2 := exclude [0,2] (fun u v => edge r21 v u) (a 8) (a 7) 2 t5 c21 (by decide +kernel)
  have t7 : a 8 ∈ [0,3] := remove (a 8) 2 [0,2,3] t6 b7
  have b8 : a 9 ≠ 4 := exclude [0,2] (fun u v => edge r22 v u) (a 9) (a 7) 4 t5 c22 (by decide +kernel)
  have t8 : a 9 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 9) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d9 b8
  have b9 : a 9 ≠ 5 := exclude [0,2] (fun u v => edge r22 v u) (a 9) (a 7) 5 t5 c22 (by decide +kernel)
  have t9 : a 9 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 9) 5 [0,1,2,3,5,6,7,8,9,10,11] t8 b9
  have b10 : a 9 ≠ 6 := exclude [0,2] (fun u v => edge r22 v u) (a 9) (a 7) 6 t5 c22 (by decide +kernel)
  have t10 : a 9 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 9) 6 [0,1,2,3,6,7,8,9,10,11] t9 b10
  have b11 : a 9 ≠ 7 := exclude [0,2] (fun u v => edge r22 v u) (a 9) (a 7) 7 t5 c22 (by decide +kernel)
  have t11 : a 9 ∈ [0,1,2,3,8,9,10,11] := remove (a 9) 7 [0,1,2,3,7,8,9,10,11] t10 b11
  have b12 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 1 t5 c24 (by decide +kernel)
  have t12 : a 21 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d21 b12
  have b13 : a 21 ≠ 2 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 2 t5 c24 (by decide +kernel)
  have t13 : a 21 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 3 t5 c24 (by decide +kernel)
  have t14 : a 21 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 21 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 4 t5 c24 (by decide +kernel)
  have t15 : a 21 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t4 (And.intro t5 (And.intro t7 (And.intro t11 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d7 : a 7 ∈ [0,2])
    (c24 : edge r24 (a 7) (a 21)=true)
    : a 21 ∈ [0,5,14,16] := by
  have b0 : a 21 ≠ 6 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 6 d7 c24 (by decide +kernel)
  have t0 : a 21 ∈ [0,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 6 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d21 b0
  have b1 : a 21 ≠ 7 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 7 d7 c24 (by decide +kernel)
  have t1 : a 21 ∈ [0,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 7 [0,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 21 ≠ 8 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 8 d7 c24 (by decide +kernel)
  have t2 : a 21 ∈ [0,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 8 [0,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 21 ≠ 9 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 9 d7 c24 (by decide +kernel)
  have t3 : a 21 ∈ [0,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 9 [0,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 21 ≠ 10 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 10 d7 c24 (by decide +kernel)
  have t4 : a 21 ∈ [0,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 10 [0,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 21 ≠ 11 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 11 d7 c24 (by decide +kernel)
  have t5 : a 21 ∈ [0,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 11 [0,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 21 ≠ 12 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 12 d7 c24 (by decide +kernel)
  have t6 : a 21 ∈ [0,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 12 [0,5,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 21 ≠ 13 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 13 d7 c24 (by decide +kernel)
  have t7 : a 21 ∈ [0,5,14,15,16,17,18,19,20,21,22,23] := remove (a 21) 13 [0,5,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 21 ≠ 15 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 15 d7 c24 (by decide +kernel)
  have t8 : a 21 ∈ [0,5,14,16,17,18,19,20,21,22,23] := remove (a 21) 15 [0,5,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 21 ≠ 17 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 17 d7 c24 (by decide +kernel)
  have t9 : a 21 ∈ [0,5,14,16,18,19,20,21,22,23] := remove (a 21) 17 [0,5,14,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 21 ≠ 18 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 18 d7 c24 (by decide +kernel)
  have t10 : a 21 ∈ [0,5,14,16,19,20,21,22,23] := remove (a 21) 18 [0,5,14,16,18,19,20,21,22,23] t9 b10
  have b11 : a 21 ≠ 19 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 19 d7 c24 (by decide +kernel)
  have t11 : a 21 ∈ [0,5,14,16,20,21,22,23] := remove (a 21) 19 [0,5,14,16,19,20,21,22,23] t10 b11
  have b12 : a 21 ≠ 20 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 20 d7 c24 (by decide +kernel)
  have t12 : a 21 ∈ [0,5,14,16,21,22,23] := remove (a 21) 20 [0,5,14,16,20,21,22,23] t11 b12
  have b13 : a 21 ≠ 21 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 21 d7 c24 (by decide +kernel)
  have t13 : a 21 ∈ [0,5,14,16,22,23] := remove (a 21) 21 [0,5,14,16,21,22,23] t12 b13
  have b14 : a 21 ≠ 22 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 22 d7 c24 (by decide +kernel)
  have t14 : a 21 ∈ [0,5,14,16,23] := remove (a 21) 22 [0,5,14,16,22,23] t13 b14
  have b15 : a 21 ≠ 23 := exclude [0,2] (fun u v => edge r24 v u) (a 21) (a 7) 23 d7 c24 (by decide +kernel)
  have t15 : a 21 ∈ [0,5,14,16] := remove (a 21) 23 [0,5,14,16,23] t14 b15
  exact t15

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_215
