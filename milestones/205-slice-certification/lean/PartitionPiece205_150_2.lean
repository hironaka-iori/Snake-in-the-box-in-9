import PartitionData205_150
namespace PartitionCover205_150
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d5 : a 5 ∈ [0])
    (d6 : a 6 ∈ [0,1,6,7,8])
    (d7 : a 7 ∈ [0])
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    : a 13 ∈ [0] ∧ a 6 ∈ [0,7,8] := by
  have b0 : a 13 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t0 : a 13 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d13 b0
  have b1 : a 13 ≠ 5 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t1 : a 13 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 13 ≠ 6 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t2 : a 13 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 13 ≠ 7 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t3 : a 13 ∈ [0,8,9,10,11,12,13,14,15,16,17] := remove (a 13) 7 [0,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 13 ≠ 8 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 8 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,9,10,11,12,13,14,15,16,17] := remove (a 13) 8 [0,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 13 ≠ 9 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 9 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,10,11,12,13,14,15,16,17] := remove (a 13) 9 [0,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 13 ≠ 10 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 10 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,11,12,13,14,15,16,17] := remove (a 13) 10 [0,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 13 ≠ 11 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 11 d5 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,12,13,14,15,16,17] := remove (a 13) 11 [0,11,12,13,14,15,16,17] t6 b7
  have b8 : a 13 ≠ 12 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 12 d5 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,13,14,15,16,17] := remove (a 13) 12 [0,12,13,14,15,16,17] t7 b8
  have b9 : a 13 ≠ 13 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 13 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,14,15,16,17] := remove (a 13) 13 [0,13,14,15,16,17] t8 b9
  have b10 : a 13 ≠ 14 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 14 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,15,16,17] := remove (a 13) 14 [0,14,15,16,17] t9 b10
  have b11 : a 13 ≠ 15 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 15 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,16,17] := remove (a 13) 15 [0,15,16,17] t10 b11
  have b12 : a 13 ≠ 16 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 16 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,17] := remove (a 13) 16 [0,16,17] t11 b12
  have b13 : a 13 ≠ 17 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 17 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0] := remove (a 13) 17 [0,17] t12 b13
  have b14 : a 6 ≠ 1 := exclude [0] (edge r17) (a 6) (a 7) 1 d7 c17 (by decide +kernel)
  have t14 : a 6 ∈ [0,6,7,8] := remove (a 6) 1 [0,1,6,7,8] d6 b14
  have b15 : a 6 ≠ 6 := exclude [0] (edge r17) (a 6) (a 7) 6 d7 c17 (by decide +kernel)
  have t15 : a 6 ∈ [0,7,8] := remove (a 6) 6 [0,6,7,8] t14 b15
  exact And.intro t13 (t15)

theorem chunk9 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,7,8])
    (d7 : a 7 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 6 ∈ [0] ∧ a 14 ∈ [0,4] ∧ a 15 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 6 ≠ 7 := exclude [0] (edge r17) (a 6) (a 7) 7 d7 c17 (by decide +kernel)
  have t0 : a 6 ∈ [0,8] := remove (a 6) 7 [0,7,8] d6 b0
  have b1 : a 6 ≠ 8 := exclude [0] (edge r17) (a 6) (a 7) 8 d7 c17 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 8 [0,8] t0 b1
  have b2 : a 14 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 1 t1 c18 (by decide +kernel)
  have t2 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b2
  have b3 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 t1 c18 (by decide +kernel)
  have t3 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 t1 c18 (by decide +kernel)
  have t4 : a 14 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 14 ≠ 5 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 5 t1 c18 (by decide +kernel)
  have t5 : a 14 ∈ [0,4,6,7,8,9,10,11] := remove (a 14) 5 [0,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 14 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 6 t1 c18 (by decide +kernel)
  have t6 : a 14 ∈ [0,4,7,8,9,10,11] := remove (a 14) 6 [0,4,6,7,8,9,10,11] t5 b6
  have b7 : a 14 ≠ 7 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 7 t1 c18 (by decide +kernel)
  have t7 : a 14 ∈ [0,4,8,9,10,11] := remove (a 14) 7 [0,4,7,8,9,10,11] t6 b7
  have b8 : a 14 ≠ 8 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 8 t1 c18 (by decide +kernel)
  have t8 : a 14 ∈ [0,4,9,10,11] := remove (a 14) 8 [0,4,8,9,10,11] t7 b8
  have b9 : a 14 ≠ 9 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 9 t1 c18 (by decide +kernel)
  have t9 : a 14 ∈ [0,4,10,11] := remove (a 14) 9 [0,4,9,10,11] t8 b9
  have b10 : a 14 ≠ 10 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 10 t1 c18 (by decide +kernel)
  have t10 : a 14 ∈ [0,4,11] := remove (a 14) 10 [0,4,10,11] t9 b10
  have b11 : a 14 ≠ 11 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 11 t1 c18 (by decide +kernel)
  have t11 : a 14 ∈ [0,4] := remove (a 14) 11 [0,4,11] t10 b11
  have b12 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d15 b12
  have b13 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 15 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 4 d7 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 15 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t11 (t15))

theorem chunk10 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17])
    (d7 : a 7 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,3])
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    : a 15 ∈ [0,1] ∧ a 8 ∈ [0,5] := by
  have b0 : a 15 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 6 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] d15 b0
  have b1 : a 15 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 7 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 15) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 15 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 8 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 15) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 15 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 9 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 15) 9 [0,1,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 15 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 10 d7 c19 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 15) 10 [0,1,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 15 ≠ 11 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 11 d7 c19 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,12,13,14,15,16,17] := remove (a 15) 11 [0,1,11,12,13,14,15,16,17] t4 b5
  have b6 : a 15 ≠ 12 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 12 d7 c19 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,13,14,15,16,17] := remove (a 15) 12 [0,1,12,13,14,15,16,17] t5 b6
  have b7 : a 15 ≠ 13 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 13 d7 c19 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,14,15,16,17] := remove (a 15) 13 [0,1,13,14,15,16,17] t6 b7
  have b8 : a 15 ≠ 14 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 14 d7 c19 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,15,16,17] := remove (a 15) 14 [0,1,14,15,16,17] t7 b8
  have b9 : a 15 ≠ 15 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 15 d7 c19 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,16,17] := remove (a 15) 15 [0,1,15,16,17] t8 b9
  have b10 : a 15 ≠ 16 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 16 d7 c19 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,17] := remove (a 15) 16 [0,1,16,17] t9 b10
  have b11 : a 15 ≠ 17 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 17 d7 c19 (by decide +kernel)
  have t11 : a 15 ∈ [0,1] := remove (a 15) 17 [0,1,17] t10 b11
  have b12 : a 8 ≠ 1 := exclude [0,3] (edge r20) (a 8) (a 9) 1 d9 c20 (by decide +kernel)
  have t12 : a 8 ∈ [0,2,3,4,5] := remove (a 8) 1 [0,1,2,3,4,5] d8 b12
  have b13 : a 8 ≠ 2 := exclude [0,3] (edge r20) (a 8) (a 9) 2 d9 c20 (by decide +kernel)
  have t13 : a 8 ∈ [0,3,4,5] := remove (a 8) 2 [0,2,3,4,5] t12 b13
  have b14 : a 8 ≠ 3 := exclude [0,3] (edge r20) (a 8) (a 9) 3 d9 c20 (by decide +kernel)
  have t14 : a 8 ∈ [0,4,5] := remove (a 8) 3 [0,3,4,5] t13 b14
  have b15 : a 8 ≠ 4 := exclude [0,3] (edge r20) (a 8) (a 9) 4 d9 c20 (by decide +kernel)
  have t15 : a 8 ∈ [0,5] := remove (a 8) 4 [0,4,5] t14 b15
  exact And.intro t11 (t15)

theorem chunk11 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,3])
    (d8 : a 8 ∈ [0,5])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0])
    (d11 : a 11 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d14 : a 14 ∈ [0,4])
    (d1 : a 1 ∈ [0,3])
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d6 : a 6 ∈ [0])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c29 : edge r29 (a 12) (a 14)=true)
    : a 9 ∈ [0] ∧ a 10 ∈ [0] ∧ a 8 ∈ [0] ∧ a 11 ∈ [0] ∧ a 15 ∈ [0] ∧ a 14 ∈ [0] ∧ a 1 ∈ [0] ∧ a 2 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 9 ≠ 3 := exclude [0,5] (fun u v => edge r20 v u) (a 9) (a 8) 3 d8 c20 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 3 [0,3] d9 b0
  have b1 : a 10 ≠ 1 := exclude [0,5] (fun u v => edge r21 v u) (a 10) (a 8) 1 d8 c21 (by decide +kernel)
  have t1 : a 10 ∈ [0,2,3,4,5] := remove (a 10) 1 [0,1,2,3,4,5] d10 b1
  have b2 : a 10 ≠ 2 := exclude [0,5] (fun u v => edge r21 v u) (a 10) (a 8) 2 d8 c21 (by decide +kernel)
  have t2 : a 10 ∈ [0,3,4,5] := remove (a 10) 2 [0,2,3,4,5] t1 b2
  have b3 : a 10 ≠ 3 := exclude [0,5] (fun u v => edge r21 v u) (a 10) (a 8) 3 d8 c21 (by decide +kernel)
  have t3 : a 10 ∈ [0,4,5] := remove (a 10) 3 [0,3,4,5] t2 b3
  have b4 : a 10 ≠ 4 := exclude [0,5] (fun u v => edge r21 v u) (a 10) (a 8) 4 d8 c21 (by decide +kernel)
  have t4 : a 10 ∈ [0,5] := remove (a 10) 4 [0,4,5] t3 b4
  have b5 : a 8 ≠ 5 := exclude [0] (edge r22) (a 8) (a 12) 5 d12 c22 (by decide +kernel)
  have t5 : a 8 ∈ [0] := remove (a 8) 5 [0,5] d8 b5
  have b6 : a 11 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 11) (a 9) 1 t0 c23 (by decide +kernel)
  have t6 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b6
  have b7 : a 10 ≠ 5 := exclude [0] (edge r25) (a 10) (a 11) 5 t6 c25 (by decide +kernel)
  have t7 : a 10 ∈ [0] := remove (a 10) 5 [0,5] t4 b7
  have b8 : a 15 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 1 t6 c27 (by decide +kernel)
  have t8 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b8
  have b9 : a 14 ≠ 4 := exclude [0] (fun u v => edge r29 v u) (a 14) (a 12) 4 d12 c29 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 4 [0,4] d14 b9
  have b10 : a 1 ≠ 3 := exclude [0,1] (edge r4) (a 1) (a 3) 3 d3 c4 (by decide +kernel)
  have t10 : a 1 ∈ [0] := remove (a 1) 3 [0,3] d1 b10
  have b11 : a 2 ≠ 1 := exclude [0] (edge r8) (a 2) (a 6) 1 d6 c8 (by decide +kernel)
  have t11 : a 2 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 2) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d2 b11
  have b12 : a 2 ≠ 2 := exclude [0] (edge r8) (a 2) (a 6) 2 d6 c8 (by decide +kernel)
  have t12 : a 2 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 2) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 2 ≠ 3 := exclude [0] (edge r8) (a 2) (a 6) 3 d6 c8 (by decide +kernel)
  have t13 : a 2 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 2) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 2 ≠ 4 := exclude [0] (edge r8) (a 2) (a 6) 4 d6 c8 (by decide +kernel)
  have t14 : a 2 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 2) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 2 ≠ 5 := exclude [0] (edge r8) (a 2) (a 6) 5 d6 c8 (by decide +kernel)
  have t15 : a 2 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 2) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t7 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t10 (t15)))))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_150
