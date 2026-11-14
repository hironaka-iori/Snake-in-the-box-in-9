import PartitionData205_206
namespace PartitionCover205_206
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,4,5,10,11])
    (d2 : a 2 ∈ [0,2])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,6])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 18 ∈ [0,1,4,5] ∧ a 7 ∈ [0,1,2,3] ∧ a 11 ∈ [0,3,4,6,7,8] ∧ a 19 ∈ [0,1,3,4,6,7] ∧ a 5 ∈ [0,2] ∧ a 12 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 18 ≠ 10 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,1,4,5,11] := remove (a 18) 10 [0,1,4,5,10,11] d18 b0
  have b1 : a 18 ≠ 11 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,4,5] := remove (a 18) 11 [0,1,4,5,11] t0 b1
  have b2 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 4 d3 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0,1,2,3,5] := remove (a 7) 4 [0,1,2,3,4,5] d7 b2
  have b3 : a 7 ≠ 5 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 5 d3 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0,1,2,3] := remove (a 7) 5 [0,1,2,3,5] t2 b3
  have b4 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,2,3,4,5,6,7,8] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8] d11 b4
  have b5 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,3,4,5,6,7,8] := remove (a 11) 2 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,3,4,6,7,8] := remove (a 11) 5 [0,3,4,5,6,7,8] t5 b6
  have b7 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,3,4,5,6,7,8] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8] d19 b7
  have b8 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,3,4,6,7,8] := remove (a 19) 5 [0,1,3,4,5,6,7,8] t7 b8
  have b9 : a 19 ≠ 8 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t9 : a 19 ∈ [0,1,3,4,6,7] := remove (a 19) 8 [0,1,3,4,6,7,8] t8 b9
  have b10 : a 5 ≠ 1 := exclude [0,6] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t10 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b10
  have b11 : a 5 ≠ 3 := exclude [0,6] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t11 : a 5 ∈ [0,2,4,5] := remove (a 5) 3 [0,2,3,4,5] t10 b11
  have b12 : a 5 ≠ 4 := exclude [0,6] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t12 : a 5 ∈ [0,2,5] := remove (a 5) 4 [0,2,4,5] t11 b12
  have b13 : a 5 ≠ 5 := exclude [0,6] (fun u v => edge r16 v u) (a 5) (a 4) 5 d4 c16 (by decide +kernel)
  have t13 : a 5 ∈ [0,2] := remove (a 5) 5 [0,2,5] t12 b13
  have b14 : a 12 ≠ 2 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b14
  have b15 : a 12 ≠ 3 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 3 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t6 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk5 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d4 : a 4 ∈ [0,6])
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 12 ∈ [0,1,12,13,22,23] := by
  have b0 : a 12 ≠ 4 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 4 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b0
  have b1 : a 12 ≠ 5 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 5 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 12 ≠ 6 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 12 ≠ 7 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 7 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 12 ≠ 8 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 12 ≠ 9 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 12 ≠ 10 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 10 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 12 ≠ 11 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 11 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 12 ≠ 14 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 14 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,12,13,15,16,17,18,19,20,21,22,23] := remove (a 12) 14 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 12 ≠ 15 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 15 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,12,13,16,17,18,19,20,21,22,23] := remove (a 12) 15 [0,1,12,13,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 12 ≠ 16 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 16 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,12,13,17,18,19,20,21,22,23] := remove (a 12) 16 [0,1,12,13,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 12 ≠ 17 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 17 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,12,13,18,19,20,21,22,23] := remove (a 12) 17 [0,1,12,13,17,18,19,20,21,22,23] t10 b11
  have b12 : a 12 ≠ 18 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 18 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,12,13,19,20,21,22,23] := remove (a 12) 18 [0,1,12,13,18,19,20,21,22,23] t11 b12
  have b13 : a 12 ≠ 19 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 19 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,12,13,20,21,22,23] := remove (a 12) 19 [0,1,12,13,19,20,21,22,23] t12 b13
  have b14 : a 12 ≠ 20 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 20 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,12,13,21,22,23] := remove (a 12) 20 [0,1,12,13,20,21,22,23] t13 b14
  have b15 : a 12 ≠ 21 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 21 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,12,13,22,23] := remove (a 12) 21 [0,1,12,13,21,22,23] t14 b15
  exact t15

theorem chunk6 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,12,13,22,23])
    (d4 : a 4 ∈ [0,6])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 12 ∈ [0,1,12,13] ∧ a 20 ∈ [0,6,16,17] := by
  have b0 : a 12 ≠ 22 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 22 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,12,13,23] := remove (a 12) 22 [0,1,12,13,22,23] d12 b0
  have b1 : a 12 ≠ 23 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 23 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,12,13] := remove (a 12) 23 [0,1,12,13,23] t0 b1
  have b2 : a 20 ≠ 1 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d20 b2
  have b3 : a 20 ≠ 2 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 20 ≠ 3 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 20 ≠ 4 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 20 ≠ 5 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 20 ≠ 7 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 20 ≠ 8 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 20) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 20 ≠ 9 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 9 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 20) 9 [0,6,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 20 ≠ 10 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 20) 10 [0,6,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 20 ≠ 11 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,6,12,13,14,15,16,17] := remove (a 20) 11 [0,6,11,12,13,14,15,16,17] t10 b11
  have b12 : a 20 ≠ 12 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 12 d4 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,6,13,14,15,16,17] := remove (a 20) 12 [0,6,12,13,14,15,16,17] t11 b12
  have b13 : a 20 ≠ 13 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 13 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,6,14,15,16,17] := remove (a 20) 13 [0,6,13,14,15,16,17] t12 b13
  have b14 : a 20 ≠ 14 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 14 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,6,15,16,17] := remove (a 20) 14 [0,6,14,15,16,17] t13 b14
  have b15 : a 20 ≠ 15 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 15 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,6,16,17] := remove (a 20) 15 [0,6,15,16,17] t14 b15
  exact And.intro t1 (t15)

theorem chunk7 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,6,16,17])
    (d4 : a 4 ∈ [0,6])
    (d7 : a 7 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 20 ∈ [0,6] ∧ a 7 ∈ [0,2] ∧ a 13 ∈ [0,1,3,4,5,11,12,14,20,21,22,23] := by
  have b0 : a 20 ≠ 16 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 16 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,6,17] := remove (a 20) 16 [0,6,16,17] d20 b0
  have b1 : a 20 ≠ 17 := exclude [0,6] (fun u v => edge r19 v u) (a 20) (a 4) 17 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,6] := remove (a 20) 17 [0,6,17] t0 b1
  have b2 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t2 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b2
  have b3 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 3 d5 c20 (by decide +kernel)
  have t3 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t2 b3
  have b4 : a 13 ≠ 2 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d13 b4
  have b5 : a 13 ≠ 6 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 6 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 13 ≠ 7 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 7 [0,1,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 13 ≠ 8 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 8 [0,1,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 13 ≠ 9 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 9 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 9 [0,1,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 13 ≠ 10 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 10 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 10 [0,1,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 13 ≠ 13 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 13 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,3,4,5,11,12,14,15,16,17,18,19,20,21,22,23] := remove (a 13) 13 [0,1,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 13 ≠ 15 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 15 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,3,4,5,11,12,14,16,17,18,19,20,21,22,23] := remove (a 13) 15 [0,1,3,4,5,11,12,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 13 ≠ 16 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 16 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,3,4,5,11,12,14,17,18,19,20,21,22,23] := remove (a 13) 16 [0,1,3,4,5,11,12,14,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 13 ≠ 17 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 17 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,3,4,5,11,12,14,18,19,20,21,22,23] := remove (a 13) 17 [0,1,3,4,5,11,12,14,17,18,19,20,21,22,23] t12 b13
  have b14 : a 13 ≠ 18 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 18 d5 c21 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,3,4,5,11,12,14,19,20,21,22,23] := remove (a 13) 18 [0,1,3,4,5,11,12,14,18,19,20,21,22,23] t13 b14
  have b15 : a 13 ≠ 19 := exclude [0,2] (fun u v => edge r21 v u) (a 13) (a 5) 19 d5 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,3,4,5,11,12,14,20,21,22,23] := remove (a 13) 19 [0,1,3,4,5,11,12,14,19,20,21,22,23] t14 b15
  exact And.intro t1 (And.intro t3 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_206
