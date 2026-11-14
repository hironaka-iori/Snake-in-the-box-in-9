import PartitionData205_189
namespace PartitionCover205_189
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,4,15,18,19,20,21,22,23])
    (d3 : a 3 ∈ [0,1])
    (d4 : a 4 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 13)=true)
    (c21 : edge r21 (a 5) (a 20)=true)
    : a 11 ∈ [0,4,15,19] ∧ a 4 ∈ [0,1] ∧ a 6 ∈ [0,1,3,4] ∧ a 12 ∈ [0,1,2,3] ∧ a 13 ∈ [0,1,2,3,4,5] ∧ a 20 ∈ [0,1,3,4,6,7,8] := by
  have b0 : a 11 ≠ 18 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 18 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,4,15,19,20,21,22,23] := remove (a 11) 18 [0,4,15,18,19,20,21,22,23] d11 b0
  have b1 : a 11 ≠ 20 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 20 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,4,15,19,21,22,23] := remove (a 11) 20 [0,4,15,19,20,21,22,23] t0 b1
  have b2 : a 11 ≠ 21 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 21 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,4,15,19,22,23] := remove (a 11) 21 [0,4,15,19,21,22,23] t1 b2
  have b3 : a 11 ≠ 22 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 22 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,4,15,19,23] := remove (a 11) 22 [0,4,15,19,22,23] t2 b3
  have b4 : a 11 ≠ 23 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 23 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,4,15,19] := remove (a 11) 23 [0,4,15,19,23] t3 b4
  have b5 : a 4 ≠ 2 := exclude [0] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0,1,3] := remove (a 4) 2 [0,1,2,3] d4 b5
  have b6 : a 4 ≠ 3 := exclude [0] (edge r16) (a 4) (a 5) 3 d5 c16 (by decide +kernel)
  have t6 : a 4 ∈ [0,1] := remove (a 4) 3 [0,1,3] t5 b6
  have b7 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 2 t6 c17 (by decide +kernel)
  have t7 : a 6 ∈ [0,1,3,4,5] := remove (a 6) 2 [0,1,2,3,4,5] d6 b7
  have b8 : a 6 ≠ 5 := exclude [0,1] (fun u v => edge r17 v u) (a 6) (a 4) 5 t6 c17 (by decide +kernel)
  have t8 : a 6 ∈ [0,1,3,4] := remove (a 6) 5 [0,1,3,4,5] t7 b8
  have b9 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 4 t6 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,2,3,5] := remove (a 12) 4 [0,1,2,3,4,5] d12 b9
  have b10 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r18 v u) (a 12) (a 4) 5 t6 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,2,3] := remove (a 12) 5 [0,1,2,3,5] t9 b10
  have b11 : a 13 ≠ 6 := exclude [0] (fun u v => edge r20 v u) (a 13) (a 5) 6 d5 c20 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,2,3,4,5,7,8] := remove (a 13) 6 [0,1,2,3,4,5,6,7,8] d13 b11
  have b12 : a 13 ≠ 7 := exclude [0] (fun u v => edge r20 v u) (a 13) (a 5) 7 d5 c20 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,3,4,5,8] := remove (a 13) 7 [0,1,2,3,4,5,7,8] t11 b12
  have b13 : a 13 ≠ 8 := exclude [0] (fun u v => edge r20 v u) (a 13) (a 5) 8 d5 c20 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,3,4,5] := remove (a 13) 8 [0,1,2,3,4,5,8] t12 b13
  have b14 : a 20 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 20) (a 5) 2 d5 c21 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,3,4,5,6,7,8] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8] d20 b14
  have b15 : a 20 ≠ 5 := exclude [0] (fun u v => edge r21 v u) (a 20) (a 5) 5 d5 c21 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,3,4,6,7,8] := remove (a 20) 5 [0,1,3,4,5,6,7,8] t14 b15
  exact And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t13 (t15)))))

theorem chunk5 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,3,4,6,7,8])
    (d5 : a 5 ∈ [0])
    (d6 : a 6 ∈ [0,1,3,4])
    (d7 : a 7 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c21 : edge r21 (a 5) (a 20)=true)
    (c22 : edge r22 (a 6) (a 7)=true)
    (c23 : edge r23 (a 6) (a 14)=true)
    : a 20 ∈ [0,1,3,4] ∧ a 6 ∈ [0,3] ∧ a 14 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := by
  have b0 : a 20 ≠ 6 := exclude [0] (fun u v => edge r21 v u) (a 20) (a 5) 6 d5 c21 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,3,4,7,8] := remove (a 20) 6 [0,1,3,4,6,7,8] d20 b0
  have b1 : a 20 ≠ 7 := exclude [0] (fun u v => edge r21 v u) (a 20) (a 5) 7 d5 c21 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,3,4,8] := remove (a 20) 7 [0,1,3,4,7,8] t0 b1
  have b2 : a 20 ≠ 8 := exclude [0] (fun u v => edge r21 v u) (a 20) (a 5) 8 d5 c21 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,3,4] := remove (a 20) 8 [0,1,3,4,8] t1 b2
  have b3 : a 6 ≠ 1 := exclude [0,1] (edge r22) (a 6) (a 7) 1 d7 c22 (by decide +kernel)
  have t3 : a 6 ∈ [0,3,4] := remove (a 6) 1 [0,1,3,4] d6 b3
  have b4 : a 6 ≠ 4 := exclude [0,1] (edge r22) (a 6) (a 7) 4 d7 c22 (by decide +kernel)
  have t4 : a 6 ∈ [0,3] := remove (a 6) 4 [0,3,4] t3 b4
  have b5 : a 14 ≠ 6 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 6 t4 c23 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d14 b5
  have b6 : a 14 ≠ 7 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 7 t4 c23 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 14 ≠ 8 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 8 t4 c23 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 14 ≠ 9 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 9 t4 c23 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 14 ≠ 10 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 10 t4 c23 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 14 ≠ 11 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 11 t4 c23 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 14 ≠ 12 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 12 t4 c23 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 12 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 14 ≠ 13 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 13 t4 c23 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 14) 13 [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 14 ≠ 14 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 14 t4 c23 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] := remove (a 14) 14 [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 14 ≠ 15 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 15 t4 c23 (by decide +kernel)
  have t14 : a 14 ∈ [0,1,2,3,4,5,16,17,18,19,20,21,22,23] := remove (a 14) 15 [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 14 ≠ 16 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 16 t4 c23 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := remove (a 14) 16 [0,1,2,3,4,5,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t2 (And.intro t4 (t15))

theorem chunk6 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,3])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,1])
    (d8 : a 8 ∈ [0,2,4,5])
    (d9 : a 9 ∈ [0,2])
    (c23 : edge r23 (a 6) (a 14)=true)
    (c24 : edge r24 (a 6) (a 21)=true)
    (c25 : edge r25 (a 7) (a 15)=true)
    (c27 : edge r27 (a 8) (a 9)=true)
    : a 14 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] ∧ a 21 ∈ [0,1,2,3] ∧ a 15 ∈ [0,1,3,4,6,7] ∧ a 8 ∈ [0,2,5] := by
  have b0 : a 14 ≠ 17 := exclude [0,3] (fun u v => edge r23 v u) (a 14) (a 6) 17 d6 c23 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := remove (a 14) 17 [0,1,2,3,4,5,17,18,19,20,21,22,23] d14 b0
  have b1 : a 21 ≠ 4 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 4 d6 c24 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 21) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d21 b1
  have b2 : a 21 ≠ 5 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 5 d6 c24 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 21) 5 [0,1,2,3,5,6,7,8,9,10,11] t1 b2
  have b3 : a 21 ≠ 6 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 6 d6 c24 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 21) 6 [0,1,2,3,6,7,8,9,10,11] t2 b3
  have b4 : a 21 ≠ 7 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 7 d6 c24 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,2,3,8,9,10,11] := remove (a 21) 7 [0,1,2,3,7,8,9,10,11] t3 b4
  have b5 : a 21 ≠ 8 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 8 d6 c24 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,2,3,9,10,11] := remove (a 21) 8 [0,1,2,3,8,9,10,11] t4 b5
  have b6 : a 21 ≠ 9 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 9 d6 c24 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,2,3,10,11] := remove (a 21) 9 [0,1,2,3,9,10,11] t5 b6
  have b7 : a 21 ≠ 10 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 10 d6 c24 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,2,3,11] := remove (a 21) 10 [0,1,2,3,10,11] t6 b7
  have b8 : a 21 ≠ 11 := exclude [0,3] (fun u v => edge r24 v u) (a 21) (a 6) 11 d6 c24 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,2,3] := remove (a 21) 11 [0,1,2,3,11] t7 b8
  have b9 : a 15 ≠ 2 := exclude [0,1] (fun u v => edge r25 v u) (a 15) (a 7) 2 d7 c25 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b9
  have b10 : a 15 ≠ 5 := exclude [0,1] (fun u v => edge r25 v u) (a 15) (a 7) 5 d7 c25 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,3,4,6,7,8,9,10,11] := remove (a 15) 5 [0,1,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 15 ≠ 8 := exclude [0,1] (fun u v => edge r25 v u) (a 15) (a 7) 8 d7 c25 (by decide +kernel)
  have t11 : a 15 ∈ [0,1,3,4,6,7,9,10,11] := remove (a 15) 8 [0,1,3,4,6,7,8,9,10,11] t10 b11
  have b12 : a 15 ≠ 9 := exclude [0,1] (fun u v => edge r25 v u) (a 15) (a 7) 9 d7 c25 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,3,4,6,7,10,11] := remove (a 15) 9 [0,1,3,4,6,7,9,10,11] t11 b12
  have b13 : a 15 ≠ 10 := exclude [0,1] (fun u v => edge r25 v u) (a 15) (a 7) 10 d7 c25 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,3,4,6,7,11] := remove (a 15) 10 [0,1,3,4,6,7,10,11] t12 b13
  have b14 : a 15 ≠ 11 := exclude [0,1] (fun u v => edge r25 v u) (a 15) (a 7) 11 d7 c25 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,3,4,6,7] := remove (a 15) 11 [0,1,3,4,6,7,11] t13 b14
  have b15 : a 8 ≠ 4 := exclude [0,2] (edge r27) (a 8) (a 9) 4 d9 c27 (by decide +kernel)
  have t15 : a 8 ∈ [0,2,5] := remove (a 8) 4 [0,2,4,5] d8 b15
  exact And.intro t0 (And.intro t8 (And.intro t14 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,2,5])
    (d9 : a 9 ∈ [0,2])
    (d12 : a 12 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d11 : a 11 ∈ [0,4,15,19])
    (d10 : a 10 ∈ [0,6,11,18])
    (d14 : a 14 ∈ [0,1,2,3,4,5,18,19,20,21,22,23])
    (c27 : edge r27 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 12)=true)
    (c33 : edge r33 (a 9) (a 24)=true)
    (c34 : edge r34 (a 10) (a 11)=true)
    (c35 : edge r35 (a 10) (a 14)=true)
    : a 8 ∈ [0,2] ∧ a 12 ∈ [0,2] ∧ a 24 ∈ [0,1,2,3,6,7,8,9] ∧ a 11 ∈ [0,19] ∧ a 10 ∈ [0,11,18] := by
  have b0 : a 8 ≠ 5 := exclude [0,2] (edge r27) (a 8) (a 9) 5 d9 c27 (by decide +kernel)
  have t0 : a 8 ∈ [0,2] := remove (a 8) 5 [0,2,5] d8 b0
  have b1 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r29 v u) (a 12) (a 8) 1 t0 c29 (by decide +kernel)
  have t1 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b1
  have b2 : a 12 ≠ 3 := exclude [0,2] (fun u v => edge r29 v u) (a 12) (a 8) 3 t0 c29 (by decide +kernel)
  have t2 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t1 b2
  have b3 : a 24 ≠ 4 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 4 d9 c33 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b3
  have b4 : a 24 ≠ 5 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 5 d9 c33 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 24 ≠ 10 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 10 d9 c33 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,2,3,6,7,8,9,11,12,13,14,15,16,17] := remove (a 24) 10 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 24 ≠ 11 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 11 d9 c33 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,2,3,6,7,8,9,12,13,14,15,16,17] := remove (a 24) 11 [0,1,2,3,6,7,8,9,11,12,13,14,15,16,17] t5 b6
  have b7 : a 24 ≠ 12 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 12 d9 c33 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,2,3,6,7,8,9,13,14,15,16,17] := remove (a 24) 12 [0,1,2,3,6,7,8,9,12,13,14,15,16,17] t6 b7
  have b8 : a 24 ≠ 13 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 13 d9 c33 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,2,3,6,7,8,9,14,15,16,17] := remove (a 24) 13 [0,1,2,3,6,7,8,9,13,14,15,16,17] t7 b8
  have b9 : a 24 ≠ 14 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 14 d9 c33 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,2,3,6,7,8,9,15,16,17] := remove (a 24) 14 [0,1,2,3,6,7,8,9,14,15,16,17] t8 b9
  have b10 : a 24 ≠ 15 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 15 d9 c33 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,2,3,6,7,8,9,16,17] := remove (a 24) 15 [0,1,2,3,6,7,8,9,15,16,17] t9 b10
  have b11 : a 24 ≠ 16 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 16 d9 c33 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,2,3,6,7,8,9,17] := remove (a 24) 16 [0,1,2,3,6,7,8,9,16,17] t10 b11
  have b12 : a 24 ≠ 17 := exclude [0,2] (fun u v => edge r33 v u) (a 24) (a 9) 17 d9 c33 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,2,3,6,7,8,9] := remove (a 24) 17 [0,1,2,3,6,7,8,9,17] t11 b12
  have b13 : a 11 ≠ 4 := exclude [0,6,11,18] (fun u v => edge r34 v u) (a 11) (a 10) 4 d10 c34 (by decide +kernel)
  have t13 : a 11 ∈ [0,15,19] := remove (a 11) 4 [0,4,15,19] d11 b13
  have b14 : a 11 ≠ 15 := exclude [0,6,11,18] (fun u v => edge r34 v u) (a 11) (a 10) 15 d10 c34 (by decide +kernel)
  have t14 : a 11 ∈ [0,19] := remove (a 11) 15 [0,15,19] t13 b14
  have b15 : a 10 ≠ 6 := exclude [0,1,2,3,4,5,18,19,20,21,22,23] (edge r35) (a 10) (a 14) 6 d14 c35 (by decide +kernel)
  have t15 : a 10 ∈ [0,11,18] := remove (a 10) 6 [0,6,11,18] d10 b15
  exact And.intro t0 (And.intro t2 (And.intro t12 (And.intro t14 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_189
