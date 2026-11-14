import PartitionData205_212
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17])
    (d3 : a 3 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 11 ∈ [0,2,12,14] ∧ a 19 ∈ [0,1,6,7,10,11] := by
  have b0 : a 11 ≠ 6 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] d11 b0
  have b1 : a 11 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,2,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,9,10,11,12,13,14,15,16,17] := remove (a 11) 8 [0,2,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,2,10,11,12,13,14,15,16,17] := remove (a 11) 9 [0,2,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 11 ≠ 10 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,2,11,12,13,14,15,16,17] := remove (a 11) 10 [0,2,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,12,13,14,15,16,17] := remove (a 11) 11 [0,2,11,12,13,14,15,16,17] t4 b5
  have b6 : a 11 ≠ 13 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 13 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,2,12,14,15,16,17] := remove (a 11) 13 [0,2,12,13,14,15,16,17] t5 b6
  have b7 : a 11 ≠ 15 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 15 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,2,12,14,16,17] := remove (a 11) 15 [0,2,12,14,15,16,17] t6 b7
  have b8 : a 11 ≠ 16 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 16 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,2,12,14,17] := remove (a 11) 16 [0,2,12,14,16,17] t7 b8
  have b9 : a 11 ≠ 17 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 17 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,2,12,14] := remove (a 11) 17 [0,2,12,14,17] t8 b9
  have b10 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t10 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b10
  have b11 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t11 : a 19 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 19 ≠ 4 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 19) 4 [0,1,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,6,7,8,9,10,11] := remove (a 19) 5 [0,1,5,6,7,8,9,10,11] t12 b13
  have b14 : a 19 ≠ 8 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,6,7,9,10,11] := remove (a 19) 8 [0,1,6,7,8,9,10,11] t13 b14
  have b15 : a 19 ≠ 9 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 9 d3 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,6,7,10,11] := remove (a 19) 9 [0,1,6,7,9,10,11] t14 b15
  exact And.intro t9 (t15)

theorem chunk9 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,6,7,10,11])
    (d3 : a 3 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d4 : a 4 ∈ [0,1,3])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,1])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 19 ∈ [0,1,6,7] ∧ a 12 ∈ [0,1,3,4,6,7,8,10,11] ∧ a 20 ∈ [0,1,2,6,7,8,9,10,11] ∧ a 13 ∈ [0,6,10,11] := by
  have b0 : a 19 ≠ 10 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 10 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,6,7,11] := remove (a 19) 10 [0,1,6,7,10,11] d19 b0
  have b1 : a 19 ≠ 11 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 11 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,6,7] := remove (a 19) 11 [0,1,6,7,11] t0 b1
  have b2 : a 12 ≠ 2 := exclude [0,1,3] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b2
  have b3 : a 12 ≠ 5 := exclude [0,1,3] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,3,4,6,7,8,9,10,11] := remove (a 12) 5 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 12 ≠ 9 := exclude [0,1,3] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,3,4,6,7,8,10,11] := remove (a 12) 9 [0,1,3,4,6,7,8,9,10,11] t3 b4
  have b5 : a 20 ≠ 3 := exclude [0,1,3] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b5
  have b6 : a 20 ≠ 4 := exclude [0,1,3] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 20) 4 [0,1,2,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 20 ≠ 5 := exclude [0,1,3] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 20) 5 [0,1,2,5,6,7,8,9,10,11] t6 b7
  have b8 : a 13 ≠ 1 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 1 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d13 b8
  have b9 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 13) 2 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 13) 3 [0,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 13 ≠ 4 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,5,6,7,8,9,10,11] := remove (a 13) 4 [0,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 13 ≠ 5 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,6,7,8,9,10,11] := remove (a 13) 5 [0,5,6,7,8,9,10,11] t11 b12
  have b13 : a 13 ≠ 7 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,6,8,9,10,11] := remove (a 13) 7 [0,6,7,8,9,10,11] t12 b13
  have b14 : a 13 ≠ 8 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,6,9,10,11] := remove (a 13) 8 [0,6,8,9,10,11] t13 b14
  have b15 : a 13 ≠ 9 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 9 d5 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,6,10,11] := remove (a 13) 9 [0,6,9,10,11] t14 b15
  exact And.intro t1 (And.intro t4 (And.intro t7 (t15)))

theorem chunk10 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,6,10,11])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,1,2,4,5,10])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d7 : a 7 ∈ [0,1,2])
    (d8 : a 8 ∈ [0,1,18,19])
    (d9 : a 9 ∈ [0,6])
    (d12 : a 12 ∈ [0,1,3,4,6,7,8,10,11])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    : a 13 ∈ [0,6] ∧ a 14 ∈ [0,1,2,3,4,5,6,8,10,11] ∧ a 22 ∈ [0,1,2,3,4,5,6,7,8,9] ∧ a 23 ∈ [0,2,3,4,6,7,8] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0,7,8,10,11] := by
  have b0 : a 13 ≠ 10 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 10 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,6,11] := remove (a 13) 10 [0,6,10,11] d13 b0
  have b1 : a 13 ≠ 11 := exclude [0,1] (fun u v => edge r21 v u) (a 13) (a 5) 11 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,6] := remove (a 13) 11 [0,6,11] t0 b1
  have b2 : a 14 ≠ 7 := exclude [0,1,2,4,5,10] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,2,3,4,5,6,8,9,10,11] := remove (a 14) 7 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b2
  have b3 : a 14 ≠ 9 := exclude [0,1,2,4,5,10] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,2,3,4,5,6,8,10,11] := remove (a 14) 9 [0,1,2,3,4,5,6,8,9,10,11] t2 b3
  have b4 : a 22 ≠ 10 := exclude [0,1,2,4,5,10] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,11] := remove (a 22) 10 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b4
  have b5 : a 22 ≠ 11 := exclude [0,1,2,4,5,10] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9] := remove (a 22) 11 [0,1,2,3,4,5,6,7,8,9,11] t4 b5
  have b6 : a 23 ≠ 1 := exclude [0,1,2] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8,9] d23 b6
  have b7 : a 23 ≠ 5 := exclude [0,1,2] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,2,3,4,6,7,8,9] := remove (a 23) 5 [0,2,3,4,5,6,7,8,9] t6 b7
  have b8 : a 23 ≠ 9 := exclude [0,1,2] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,2,3,4,6,7,8] := remove (a 23) 9 [0,2,3,4,6,7,8,9] t7 b8
  have b9 : a 8 ≠ 1 := exclude [0,6] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t9 : a 8 ∈ [0,18,19] := remove (a 8) 1 [0,1,18,19] d8 b9
  have b10 : a 8 ≠ 19 := exclude [0,6] (edge r28) (a 8) (a 9) 19 d9 c28 (by decide +kernel)
  have t10 : a 8 ∈ [0,18] := remove (a 8) 19 [0,18,19] t9 b10
  have b11 : a 8 ≠ 18 := exclude [0,1,3,4,6,7,8,10,11] (edge r30) (a 8) (a 12) 18 d12 c30 (by decide +kernel)
  have t11 : a 8 ∈ [0] := remove (a 8) 18 [0,18] t10 b11
  have b12 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 t11 c30 (by decide +kernel)
  have t12 : a 12 ∈ [0,3,4,6,7,8,10,11] := remove (a 12) 1 [0,1,3,4,6,7,8,10,11] d12 b12
  have b13 : a 12 ≠ 3 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 3 t11 c30 (by decide +kernel)
  have t13 : a 12 ∈ [0,4,6,7,8,10,11] := remove (a 12) 3 [0,3,4,6,7,8,10,11] t12 b13
  have b14 : a 12 ≠ 4 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 4 t11 c30 (by decide +kernel)
  have t14 : a 12 ∈ [0,6,7,8,10,11] := remove (a 12) 4 [0,4,6,7,8,10,11] t13 b14
  have b15 : a 12 ≠ 6 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 6 t11 c30 (by decide +kernel)
  have t15 : a 12 ∈ [0,7,8,10,11] := remove (a 12) 6 [0,6,7,8,10,11] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t8 (And.intro t11 (t15)))))

theorem chunk11 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,7,8,10,11])
    (d8 : a 8 ∈ [0])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 12 ∈ [0] ∧ a 24 ∈ [0,12,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 12 ≠ 7 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 7 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0,8,10,11] := remove (a 12) 7 [0,7,8,10,11] d12 b0
  have b1 : a 12 ≠ 8 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 8 d8 c30 (by decide +kernel)
  have t1 : a 12 ∈ [0,10,11] := remove (a 12) 8 [0,8,10,11] t0 b1
  have b2 : a 12 ≠ 10 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 10 d8 c30 (by decide +kernel)
  have t2 : a 12 ∈ [0,11] := remove (a 12) 10 [0,10,11] t1 b2
  have b3 : a 12 ≠ 11 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 11 d8 c30 (by decide +kernel)
  have t3 : a 12 ∈ [0] := remove (a 12) 11 [0,11] t2 b3
  have b4 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d24 b4
  have b5 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 24 ≠ 5 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 24 ≠ 7 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 24 ≠ 9 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 24 ≠ 10 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 24 ≠ 11 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 24 ≠ 13 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,12,14,15,16,17,18,19,20,21,22,23] := remove (a 24) 13 [0,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (t15)

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_212
