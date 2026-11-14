import PartitionData205_114
namespace PartitionCover205_114
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21])
    (d4 : a 4 ∈ [0,3])
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 12 ∈ [0,3,18,19] := by
  have b0 : a 12 ≠ 4 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 4 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] d12 b0
  have b1 : a 12 ≠ 5 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 5 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t0 b1
  have b2 : a 12 ≠ 6 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 6 d4 c14 (by decide +kernel)
  have t2 : a 12 ∈ [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 6 [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t1 b2
  have b3 : a 12 ≠ 7 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 7 d4 c14 (by decide +kernel)
  have t3 : a 12 ∈ [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 7 [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t2 b3
  have b4 : a 12 ≠ 8 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 8 d4 c14 (by decide +kernel)
  have t4 : a 12 ∈ [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 8 [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t3 b4
  have b5 : a 12 ≠ 9 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 9 d4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [0,3,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 9 [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21] t4 b5
  have b6 : a 12 ≠ 10 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 10 d4 c14 (by decide +kernel)
  have t6 : a 12 ∈ [0,3,11,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 10 [0,3,10,11,12,13,14,15,16,17,18,19,20,21] t5 b6
  have b7 : a 12 ≠ 11 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 11 d4 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0,3,12,13,14,15,16,17,18,19,20,21] := remove (a 12) 11 [0,3,11,12,13,14,15,16,17,18,19,20,21] t6 b7
  have b8 : a 12 ≠ 12 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 12 d4 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0,3,13,14,15,16,17,18,19,20,21] := remove (a 12) 12 [0,3,12,13,14,15,16,17,18,19,20,21] t7 b8
  have b9 : a 12 ≠ 13 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 13 d4 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0,3,14,15,16,17,18,19,20,21] := remove (a 12) 13 [0,3,13,14,15,16,17,18,19,20,21] t8 b9
  have b10 : a 12 ≠ 14 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 14 d4 c14 (by decide +kernel)
  have t10 : a 12 ∈ [0,3,15,16,17,18,19,20,21] := remove (a 12) 14 [0,3,14,15,16,17,18,19,20,21] t9 b10
  have b11 : a 12 ≠ 15 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 15 d4 c14 (by decide +kernel)
  have t11 : a 12 ∈ [0,3,16,17,18,19,20,21] := remove (a 12) 15 [0,3,15,16,17,18,19,20,21] t10 b11
  have b12 : a 12 ≠ 16 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 16 d4 c14 (by decide +kernel)
  have t12 : a 12 ∈ [0,3,17,18,19,20,21] := remove (a 12) 16 [0,3,16,17,18,19,20,21] t11 b12
  have b13 : a 12 ≠ 17 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 17 d4 c14 (by decide +kernel)
  have t13 : a 12 ∈ [0,3,18,19,20,21] := remove (a 12) 17 [0,3,17,18,19,20,21] t12 b13
  have b14 : a 12 ≠ 20 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 20 d4 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,3,18,19,21] := remove (a 12) 20 [0,3,18,19,20,21] t13 b14
  have b15 : a 12 ≠ 21 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 21 d4 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,3,18,19] := remove (a 12) 21 [0,3,18,19,21] t14 b15
  exact t15

theorem chunk5 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21])
    (d5 : a 5 ∈ [0,3])
    (c15 : edge r15 (a 5) (a 7)=true)
    : a 7 ∈ [0,3,18,19,20,21] := by
  have b0 : a 7 ≠ 1 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 1 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] d7 b0
  have b1 : a 7 ≠ 2 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 2 d5 c15 (by decide +kernel)
  have t1 : a 7 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t0 b1
  have b2 : a 7 ≠ 4 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 4 d5 c15 (by decide +kernel)
  have t2 : a 7 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t1 b2
  have b3 : a 7 ≠ 5 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 5 d5 c15 (by decide +kernel)
  have t3 : a 7 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t2 b3
  have b4 : a 7 ≠ 6 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 6 d5 c15 (by decide +kernel)
  have t4 : a 7 ∈ [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 6 [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t3 b4
  have b5 : a 7 ≠ 7 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 7 d5 c15 (by decide +kernel)
  have t5 : a 7 ∈ [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 7 [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t4 b5
  have b6 : a 7 ≠ 8 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 8 d5 c15 (by decide +kernel)
  have t6 : a 7 ∈ [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 8 [0,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21] t5 b6
  have b7 : a 7 ≠ 9 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 9 d5 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0,3,10,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 9 [0,3,9,10,11,12,13,14,15,16,17,18,19,20,21] t6 b7
  have b8 : a 7 ≠ 10 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 10 d5 c15 (by decide +kernel)
  have t8 : a 7 ∈ [0,3,11,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 10 [0,3,10,11,12,13,14,15,16,17,18,19,20,21] t7 b8
  have b9 : a 7 ≠ 11 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 11 d5 c15 (by decide +kernel)
  have t9 : a 7 ∈ [0,3,12,13,14,15,16,17,18,19,20,21] := remove (a 7) 11 [0,3,11,12,13,14,15,16,17,18,19,20,21] t8 b9
  have b10 : a 7 ≠ 12 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 12 d5 c15 (by decide +kernel)
  have t10 : a 7 ∈ [0,3,13,14,15,16,17,18,19,20,21] := remove (a 7) 12 [0,3,12,13,14,15,16,17,18,19,20,21] t9 b10
  have b11 : a 7 ≠ 13 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 13 d5 c15 (by decide +kernel)
  have t11 : a 7 ∈ [0,3,14,15,16,17,18,19,20,21] := remove (a 7) 13 [0,3,13,14,15,16,17,18,19,20,21] t10 b11
  have b12 : a 7 ≠ 14 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 14 d5 c15 (by decide +kernel)
  have t12 : a 7 ∈ [0,3,15,16,17,18,19,20,21] := remove (a 7) 14 [0,3,14,15,16,17,18,19,20,21] t11 b12
  have b13 : a 7 ≠ 15 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 15 d5 c15 (by decide +kernel)
  have t13 : a 7 ∈ [0,3,16,17,18,19,20,21] := remove (a 7) 15 [0,3,15,16,17,18,19,20,21] t12 b13
  have b14 : a 7 ≠ 16 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 16 d5 c15 (by decide +kernel)
  have t14 : a 7 ∈ [0,3,17,18,19,20,21] := remove (a 7) 16 [0,3,16,17,18,19,20,21] t13 b14
  have b15 : a 7 ≠ 17 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 17 d5 c15 (by decide +kernel)
  have t15 : a 7 ∈ [0,3,18,19,20,21] := remove (a 7) 17 [0,3,17,18,19,20,21] t14 b15
  exact t15

theorem chunk6 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,3,18,19,20,21])
    (d5 : a 5 ∈ [0,3])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (d6 : a 6 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7])
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 7 ∈ [0,18] ∧ a 13 ∈ [0,1,6,7] ∧ a 14 ∈ [0,6] ∧ a 15 ∈ [0,3,4,5,6,7] := by
  have b0 : a 7 ≠ 20 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 20 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0,3,18,19,21] := remove (a 7) 20 [0,3,18,19,20,21] d7 b0
  have b1 : a 7 ≠ 21 := exclude [0,3] (fun u v => edge r15 v u) (a 7) (a 5) 21 d5 c15 (by decide +kernel)
  have t1 : a 7 ∈ [0,3,18,19] := remove (a 7) 21 [0,3,18,19,21] t0 b1
  have b2 : a 13 ≠ 2 := exclude [0,3] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,3,4,5,6,7] := remove (a 13) 2 [0,1,2,3,4,5,6,7] d13 b2
  have b3 : a 13 ≠ 3 := exclude [0,3] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,4,5,6,7] := remove (a 13) 3 [0,1,3,4,5,6,7] t2 b3
  have b4 : a 13 ≠ 4 := exclude [0,3] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,5,6,7] := remove (a 13) 4 [0,1,4,5,6,7] t3 b4
  have b5 : a 13 ≠ 5 := exclude [0,3] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,6,7] := remove (a 13) 5 [0,1,5,6,7] t4 b5
  have b6 : a 7 ≠ 3 := exclude [0,6] (fun u v => edge r17 v u) (a 7) (a 6) 3 d6 c17 (by decide +kernel)
  have t6 : a 7 ∈ [0,18,19] := remove (a 7) 3 [0,3,18,19] t1 b6
  have b7 : a 7 ≠ 19 := exclude [0,6] (fun u v => edge r17 v u) (a 7) (a 6) 19 d6 c17 (by decide +kernel)
  have t7 : a 7 ∈ [0,18] := remove (a 7) 19 [0,18,19] t6 b7
  have b8 : a 14 ≠ 1 := exclude [0,6] (fun u v => edge r18 v u) (a 14) (a 6) 1 d6 c18 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,3,4,5,6,7] := remove (a 14) 1 [0,1,2,3,4,5,6,7] d14 b8
  have b9 : a 14 ≠ 2 := exclude [0,6] (fun u v => edge r18 v u) (a 14) (a 6) 2 d6 c18 (by decide +kernel)
  have t9 : a 14 ∈ [0,3,4,5,6,7] := remove (a 14) 2 [0,2,3,4,5,6,7] t8 b9
  have b10 : a 14 ≠ 3 := exclude [0,6] (fun u v => edge r18 v u) (a 14) (a 6) 3 d6 c18 (by decide +kernel)
  have t10 : a 14 ∈ [0,4,5,6,7] := remove (a 14) 3 [0,3,4,5,6,7] t9 b10
  have b11 : a 14 ≠ 4 := exclude [0,6] (fun u v => edge r18 v u) (a 14) (a 6) 4 d6 c18 (by decide +kernel)
  have t11 : a 14 ∈ [0,5,6,7] := remove (a 14) 4 [0,4,5,6,7] t10 b11
  have b12 : a 14 ≠ 5 := exclude [0,6] (fun u v => edge r18 v u) (a 14) (a 6) 5 d6 c18 (by decide +kernel)
  have t12 : a 14 ∈ [0,6,7] := remove (a 14) 5 [0,5,6,7] t11 b12
  have b13 : a 14 ≠ 7 := exclude [0,6] (fun u v => edge r18 v u) (a 14) (a 6) 7 d6 c18 (by decide +kernel)
  have t13 : a 14 ∈ [0,6] := remove (a 14) 7 [0,6,7] t12 b13
  have b14 : a 15 ≠ 1 := exclude [0,18] (fun u v => edge r19 v u) (a 15) (a 7) 1 t7 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,2,3,4,5,6,7] := remove (a 15) 1 [0,1,2,3,4,5,6,7] d15 b14
  have b15 : a 15 ≠ 2 := exclude [0,18] (fun u v => edge r19 v u) (a 15) (a 7) 2 t7 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,3,4,5,6,7] := remove (a 15) 2 [0,2,3,4,5,6,7] t14 b15
  exact And.intro t7 (And.intro t5 (And.intro t13 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,3,4,5,6,7])
    (d7 : a 7 ∈ [0,18])
    (d8 : a 8 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,3])
    (d10 : a 10 ∈ [0,1,2,3,18,19,20,21])
    (d12 : a 12 ∈ [0,3,18,19])
    (d11 : a 11 ∈ [0,5,6,12,18,23])
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    : a 15 ∈ [0,6] ∧ a 8 ∈ [0,3] ∧ a 10 ∈ [0,2,18,20] ∧ a 12 ∈ [0,18] ∧ a 11 ∈ [0,18] := by
  have b0 : a 15 ≠ 3 := exclude [0,18] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,4,5,6,7] := remove (a 15) 3 [0,3,4,5,6,7] d15 b0
  have b1 : a 15 ≠ 4 := exclude [0,18] (fun u v => edge r19 v u) (a 15) (a 7) 4 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,5,6,7] := remove (a 15) 4 [0,4,5,6,7] t0 b1
  have b2 : a 15 ≠ 5 := exclude [0,18] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,6,7] := remove (a 15) 5 [0,5,6,7] t1 b2
  have b3 : a 15 ≠ 7 := exclude [0,18] (fun u v => edge r19 v u) (a 15) (a 7) 7 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,6] := remove (a 15) 7 [0,6,7] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0,3] (edge r20) (a 8) (a 9) 1 d9 c20 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b4
  have b5 : a 8 ≠ 2 := exclude [0,3] (edge r20) (a 8) (a 9) 2 d9 c20 (by decide +kernel)
  have t5 : a 8 ∈ [0,3] := remove (a 8) 2 [0,2,3] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,3] (fun u v => edge r21 v u) (a 10) (a 8) 1 t5 c21 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3,18,19,20,21] := remove (a 10) 1 [0,1,2,3,18,19,20,21] d10 b6
  have b7 : a 10 ≠ 3 := exclude [0,3] (fun u v => edge r21 v u) (a 10) (a 8) 3 t5 c21 (by decide +kernel)
  have t7 : a 10 ∈ [0,2,18,19,20,21] := remove (a 10) 3 [0,2,3,18,19,20,21] t6 b7
  have b8 : a 10 ≠ 19 := exclude [0,3] (fun u v => edge r21 v u) (a 10) (a 8) 19 t5 c21 (by decide +kernel)
  have t8 : a 10 ∈ [0,2,18,20,21] := remove (a 10) 19 [0,2,18,19,20,21] t7 b8
  have b9 : a 10 ≠ 21 := exclude [0,3] (fun u v => edge r21 v u) (a 10) (a 8) 21 t5 c21 (by decide +kernel)
  have t9 : a 10 ∈ [0,2,18,20] := remove (a 10) 21 [0,2,18,20,21] t8 b9
  have b10 : a 12 ≠ 3 := exclude [0,3] (fun u v => edge r22 v u) (a 12) (a 8) 3 t5 c22 (by decide +kernel)
  have t10 : a 12 ∈ [0,18,19] := remove (a 12) 3 [0,3,18,19] d12 b10
  have b11 : a 12 ≠ 19 := exclude [0,3] (fun u v => edge r22 v u) (a 12) (a 8) 19 t5 c22 (by decide +kernel)
  have t11 : a 12 ∈ [0,18] := remove (a 12) 19 [0,18,19] t10 b11
  have b12 : a 11 ≠ 5 := exclude [0,3] (fun u v => edge r23 v u) (a 11) (a 9) 5 d9 c23 (by decide +kernel)
  have t12 : a 11 ∈ [0,6,12,18,23] := remove (a 11) 5 [0,5,6,12,18,23] d11 b12
  have b13 : a 11 ≠ 6 := exclude [0,3] (fun u v => edge r23 v u) (a 11) (a 9) 6 d9 c23 (by decide +kernel)
  have t13 : a 11 ∈ [0,12,18,23] := remove (a 11) 6 [0,6,12,18,23] t12 b13
  have b14 : a 11 ≠ 12 := exclude [0,3] (fun u v => edge r23 v u) (a 11) (a 9) 12 d9 c23 (by decide +kernel)
  have t14 : a 11 ∈ [0,18,23] := remove (a 11) 12 [0,12,18,23] t13 b14
  have b15 : a 11 ≠ 23 := exclude [0,3] (fun u v => edge r23 v u) (a 11) (a 9) 23 d9 c23 (by decide +kernel)
  have t15 : a 11 ∈ [0,18] := remove (a 11) 23 [0,18,23] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t9 (And.intro t11 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_114
