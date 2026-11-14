import PartitionData205_183
namespace PartitionCover205_183
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,4,5])
    (d3 : a 3 ∈ [0,1])
    (d4 : a 4 ∈ [0,2,3,5])
    (d5 : a 5 ∈ [0,3,6,7])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 19)=true)
    : a 11 ∈ [0,1] ∧ a 4 ∈ [0,3] ∧ a 5 ∈ [0,3] ∧ a 12 ∈ [0,1,3,4,6,9] ∧ a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17] := by
  have b0 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,1,5] := remove (a 11) 4 [0,1,4,5] d11 b0
  have b1 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,1] := remove (a 11) 5 [0,1,5] t0 b1
  have b2 : a 4 ≠ 2 := exclude [0,3,6,7] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t2 : a 4 ∈ [0,3,5] := remove (a 4) 2 [0,2,3,5] d4 b2
  have b3 : a 4 ≠ 5 := exclude [0,3,6,7] (edge r16) (a 4) (a 5) 5 d5 c16 (by decide +kernel)
  have t3 : a 4 ∈ [0,3] := remove (a 4) 5 [0,3,5] t2 b3
  have b4 : a 5 ≠ 6 := exclude [0,3] (fun u v => edge r16 v u) (a 5) (a 4) 6 t3 c16 (by decide +kernel)
  have t4 : a 5 ∈ [0,3,7] := remove (a 5) 6 [0,3,6,7] d5 b4
  have b5 : a 5 ≠ 7 := exclude [0,3] (fun u v => edge r16 v u) (a 5) (a 4) 7 t3 c16 (by decide +kernel)
  have t5 : a 5 ∈ [0,3] := remove (a 5) 7 [0,3,7] t4 b5
  have b6 : a 12 ≠ 2 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 2 t3 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b6
  have b7 : a 12 ≠ 5 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 5 t3 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,3,4,6,7,8,9,10,11] := remove (a 12) 5 [0,1,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 12 ≠ 7 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 7 t3 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,3,4,6,8,9,10,11] := remove (a 12) 7 [0,1,3,4,6,7,8,9,10,11] t7 b8
  have b9 : a 12 ≠ 8 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 8 t3 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,3,4,6,9,10,11] := remove (a 12) 8 [0,1,3,4,6,8,9,10,11] t8 b9
  have b10 : a 12 ≠ 10 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 10 t3 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,3,4,6,9,11] := remove (a 12) 10 [0,1,3,4,6,9,10,11] t9 b10
  have b11 : a 12 ≠ 11 := exclude [0,3] (fun u v => edge r18 v u) (a 12) (a 4) 11 t3 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,3,4,6,9] := remove (a 12) 11 [0,1,3,4,6,9,11] t10 b11
  have b12 : a 19 ≠ 12 := exclude [0,3] (fun u v => edge r19 v u) (a 19) (a 4) 12 t3 c19 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] := remove (a 19) 12 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d19 b12
  have b13 : a 19 ≠ 13 := exclude [0,3] (fun u v => edge r19 v u) (a 19) (a 4) 13 t3 c19 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] := remove (a 19) 13 [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17] t12 b13
  have b14 : a 19 ≠ 14 := exclude [0,3] (fun u v => edge r19 v u) (a 19) (a 4) 14 t3 c19 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] := remove (a 19) 14 [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17] t13 b14
  have b15 : a 19 ≠ 15 := exclude [0,3] (fun u v => edge r19 v u) (a 19) (a 4) 15 t3 c19 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17] := remove (a 19) 15 [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t11 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17])
    (d4 : a 4 ∈ [0,3])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d5 : a 5 ∈ [0,3])
    (c19 : edge r19 (a 4) (a 19)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] ∧ a 13 ∈ [0,1,2,3,12,13,14,15,22,23] := by
  have b0 : a 19 ≠ 16 := exclude [0,3] (fun u v => edge r19 v u) (a 19) (a 4) 16 d4 c19 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,17] := remove (a 19) 16 [0,1,2,3,4,5,6,7,8,9,10,11,16,17] d19 b0
  have b1 : a 19 ≠ 17 := exclude [0,3] (fun u v => edge r19 v u) (a 19) (a 4) 17 d4 c19 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 17 [0,1,2,3,4,5,6,7,8,9,10,11,17] t0 b1
  have b2 : a 13 ≠ 4 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d13 b2
  have b3 : a 13 ≠ 5 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 13 ≠ 6 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 13 ≠ 7 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 13 ≠ 8 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 13 ≠ 9 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 9 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 13 ≠ 10 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 10 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 13 ≠ 11 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 11 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 13 ≠ 16 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 16 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,2,3,12,13,14,15,17,18,19,20,21,22,23] := remove (a 13) 16 [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 13 ≠ 17 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 17 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,2,3,12,13,14,15,18,19,20,21,22,23] := remove (a 13) 17 [0,1,2,3,12,13,14,15,17,18,19,20,21,22,23] t10 b11
  have b12 : a 13 ≠ 18 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 18 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,3,12,13,14,15,19,20,21,22,23] := remove (a 13) 18 [0,1,2,3,12,13,14,15,18,19,20,21,22,23] t11 b12
  have b13 : a 13 ≠ 19 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 19 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,3,12,13,14,15,20,21,22,23] := remove (a 13) 19 [0,1,2,3,12,13,14,15,19,20,21,22,23] t12 b13
  have b14 : a 13 ≠ 20 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 20 d5 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,2,3,12,13,14,15,21,22,23] := remove (a 13) 20 [0,1,2,3,12,13,14,15,20,21,22,23] t13 b14
  have b15 : a 13 ≠ 21 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 21 d5 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,2,3,12,13,14,15,22,23] := remove (a 13) 21 [0,1,2,3,12,13,14,15,21,22,23] t14 b15
  exact And.intro t1 (t15)

theorem chunk6 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,3,12,13,14,15,22,23])
    (d5 : a 5 ∈ [0,3])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 20)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 13 ∈ [0,1,2,3,12,13,14,15] ∧ a 20 ∈ [0,1] ∧ a 6 ∈ [0,2] ∧ a 14 ∈ [0,2,4,5,6,7,8,9,10,11] := by
  have b0 : a 13 ≠ 22 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 22 d5 c21 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,2,3,12,13,14,15,23] := remove (a 13) 22 [0,1,2,3,12,13,14,15,22,23] d13 b0
  have b1 : a 13 ≠ 23 := exclude [0,3] (fun u v => edge r21 v u) (a 13) (a 5) 23 d5 c21 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,2,3,12,13,14,15] := remove (a 13) 23 [0,1,2,3,12,13,14,15,23] t0 b1
  have b2 : a 20 ≠ 2 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 2 d5 c22 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b2
  have b3 : a 20 ≠ 3 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 3 d5 c22 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 20 ≠ 4 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 4 d5 c22 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 20) 4 [0,1,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 20 ≠ 5 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 5 d5 c22 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,6,7,8,9,10,11] := remove (a 20) 5 [0,1,5,6,7,8,9,10,11] t4 b5
  have b6 : a 20 ≠ 6 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 6 d5 c22 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,7,8,9,10,11] := remove (a 20) 6 [0,1,6,7,8,9,10,11] t5 b6
  have b7 : a 20 ≠ 7 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 7 d5 c22 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,8,9,10,11] := remove (a 20) 7 [0,1,7,8,9,10,11] t6 b7
  have b8 : a 20 ≠ 8 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 8 d5 c22 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,9,10,11] := remove (a 20) 8 [0,1,8,9,10,11] t7 b8
  have b9 : a 20 ≠ 9 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 9 d5 c22 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,10,11] := remove (a 20) 9 [0,1,9,10,11] t8 b9
  have b10 : a 20 ≠ 10 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 10 d5 c22 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,11] := remove (a 20) 10 [0,1,10,11] t9 b10
  have b11 : a 20 ≠ 11 := exclude [0,3] (fun u v => edge r22 v u) (a 20) (a 5) 11 d5 c22 (by decide +kernel)
  have t11 : a 20 ∈ [0,1] := remove (a 20) 11 [0,1,11] t10 b11
  have b12 : a 6 ≠ 1 := exclude [0] (edge r23) (a 6) (a 7) 1 d7 c23 (by decide +kernel)
  have t12 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b12
  have b13 : a 6 ≠ 3 := exclude [0] (edge r23) (a 6) (a 7) 3 d7 c23 (by decide +kernel)
  have t13 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t12 b13
  have b14 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 1 t13 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b14
  have b15 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 t13 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t11 (And.intro t13 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,2])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0])
    (d9 : a 9 ∈ [0,1,2])
    (d8 : a 8 ∈ [0,1,2,3])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 22)=true)
    (c27 : edge r27 (a 8) (a 9)=true)
    : a 14 ∈ [0,2] ∧ a 22 ∈ [0,2] ∧ a 9 ∈ [0,1] := by
  have b0 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 14) 4 [0,2,4,5,6,7,8,9,10,11] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,6,7,8,9,10,11] := remove (a 14) 5 [0,2,5,6,7,8,9,10,11] t0 b1
  have b2 : a 14 ≠ 6 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,2,7,8,9,10,11] := remove (a 14) 6 [0,2,6,7,8,9,10,11] t1 b2
  have b3 : a 14 ≠ 7 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,8,9,10,11] := remove (a 14) 7 [0,2,7,8,9,10,11] t2 b3
  have b4 : a 14 ≠ 8 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,2,9,10,11] := remove (a 14) 8 [0,2,8,9,10,11] t3 b4
  have b5 : a 14 ≠ 9 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,2,10,11] := remove (a 14) 9 [0,2,9,10,11] t4 b5
  have b6 : a 14 ≠ 10 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 10 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,2,11] := remove (a 14) 10 [0,2,10,11] t5 b6
  have b7 : a 14 ≠ 11 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 11 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,2] := remove (a 14) 11 [0,2,11] t6 b7
  have b8 : a 22 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 22) (a 7) 1 d7 c26 (by decide +kernel)
  have t8 : a 22 ∈ [0,2,3,4,5,6,7,8] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8] d22 b8
  have b9 : a 22 ≠ 3 := exclude [0] (fun u v => edge r26 v u) (a 22) (a 7) 3 d7 c26 (by decide +kernel)
  have t9 : a 22 ∈ [0,2,4,5,6,7,8] := remove (a 22) 3 [0,2,3,4,5,6,7,8] t8 b9
  have b10 : a 22 ≠ 4 := exclude [0] (fun u v => edge r26 v u) (a 22) (a 7) 4 d7 c26 (by decide +kernel)
  have t10 : a 22 ∈ [0,2,5,6,7,8] := remove (a 22) 4 [0,2,4,5,6,7,8] t9 b10
  have b11 : a 22 ≠ 5 := exclude [0] (fun u v => edge r26 v u) (a 22) (a 7) 5 d7 c26 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,6,7,8] := remove (a 22) 5 [0,2,5,6,7,8] t10 b11
  have b12 : a 22 ≠ 6 := exclude [0] (fun u v => edge r26 v u) (a 22) (a 7) 6 d7 c26 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,7,8] := remove (a 22) 6 [0,2,6,7,8] t11 b12
  have b13 : a 22 ≠ 7 := exclude [0] (fun u v => edge r26 v u) (a 22) (a 7) 7 d7 c26 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,8] := remove (a 22) 7 [0,2,7,8] t12 b13
  have b14 : a 22 ≠ 8 := exclude [0] (fun u v => edge r26 v u) (a 22) (a 7) 8 d7 c26 (by decide +kernel)
  have t14 : a 22 ∈ [0,2] := remove (a 22) 8 [0,2,8] t13 b14
  have b15 : a 9 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r27 v u) (a 9) (a 8) 2 d8 c27 (by decide +kernel)
  have t15 : a 9 ∈ [0,1] := remove (a 9) 2 [0,1,2] d9 b15
  exact And.intro t7 (And.intro t14 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_183
