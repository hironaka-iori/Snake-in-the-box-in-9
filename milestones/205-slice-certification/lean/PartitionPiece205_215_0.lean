import PartitionData205_215
namespace PartitionCover205_215
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d1 : a 1 ∈ [0])
    (d10 : a 10 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c4 : edge r4 (a 1) (a 4)=true)
    (c8 : edge r8 (a 2) (a 10)=true)
    (c9 : edge r9 (a 3) (a 4)=true)
    (c10 : edge r10 (a 3) (a 5)=true)
    : a 4 ∈ [0,3] ∧ a 10 ∈ [0,2] ∧ a 5 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 1 d1 c4 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d4 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 2 d1 c4 (by decide +kernel)
  have t1 : a 4 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 4) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t0 b1
  have b2 : a 4 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 4 d1 c4 (by decide +kernel)
  have t2 : a 4 ∈ [0,3,5,6,7,8,9,10,11,12,13] := remove (a 4) 4 [0,3,4,5,6,7,8,9,10,11,12,13] t1 b2
  have b3 : a 4 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 5 d1 c4 (by decide +kernel)
  have t3 : a 4 ∈ [0,3,6,7,8,9,10,11,12,13] := remove (a 4) 5 [0,3,5,6,7,8,9,10,11,12,13] t2 b3
  have b4 : a 4 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 6 d1 c4 (by decide +kernel)
  have t4 : a 4 ∈ [0,3,7,8,9,10,11,12,13] := remove (a 4) 6 [0,3,6,7,8,9,10,11,12,13] t3 b4
  have b5 : a 4 ≠ 7 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 7 d1 c4 (by decide +kernel)
  have t5 : a 4 ∈ [0,3,8,9,10,11,12,13] := remove (a 4) 7 [0,3,7,8,9,10,11,12,13] t4 b5
  have b6 : a 4 ≠ 10 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 10 d1 c4 (by decide +kernel)
  have t6 : a 4 ∈ [0,3,8,9,11,12,13] := remove (a 4) 10 [0,3,8,9,10,11,12,13] t5 b6
  have b7 : a 4 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 11 d1 c4 (by decide +kernel)
  have t7 : a 4 ∈ [0,3,8,9,12,13] := remove (a 4) 11 [0,3,8,9,11,12,13] t6 b7
  have b8 : a 4 ≠ 12 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 12 d1 c4 (by decide +kernel)
  have t8 : a 4 ∈ [0,3,8,9,13] := remove (a 4) 12 [0,3,8,9,12,13] t7 b8
  have b9 : a 4 ≠ 13 := exclude [0] (fun u v => edge r4 v u) (a 4) (a 1) 13 d1 c4 (by decide +kernel)
  have t9 : a 4 ∈ [0,3,8,9] := remove (a 4) 13 [0,3,8,9,13] t8 b9
  have b10 : a 10 ≠ 1 := exclude [0,1] (fun u v => edge r8 v u) (a 10) (a 2) 1 d2 c8 (by decide +kernel)
  have t10 : a 10 ∈ [0,2] := remove (a 10) 1 [0,1,2] d10 b10
  have b11 : a 4 ≠ 8 := exclude [0] (fun u v => edge r9 v u) (a 4) (a 3) 8 d3 c9 (by decide +kernel)
  have t11 : a 4 ∈ [0,3,9] := remove (a 4) 8 [0,3,8,9] t9 b11
  have b12 : a 4 ≠ 9 := exclude [0] (fun u v => edge r9 v u) (a 4) (a 3) 9 d3 c9 (by decide +kernel)
  have t12 : a 4 ∈ [0,3] := remove (a 4) 9 [0,3,9] t11 b12
  have b13 : a 5 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 2 d3 c10 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d5 b13
  have b14 : a 5 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 3 d3 c10 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 5 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 4 d3 c10 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t12 (And.intro t10 (t15))

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d3 : a 3 ∈ [0])
    (c10 : edge r10 (a 3) (a 5)=true)
    : a 5 ∈ [0,1,18,19,23] := by
  have b0 : a 5 ≠ 5 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 5 d3 c10 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d5 b0
  have b1 : a 5 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 6 d3 c10 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 5 ≠ 7 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 7 d3 c10 (by decide +kernel)
  have t2 : a 5 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 5 ≠ 8 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 8 d3 c10 (by decide +kernel)
  have t3 : a 5 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 5 ≠ 9 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 9 d3 c10 (by decide +kernel)
  have t4 : a 5 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 5 ≠ 10 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 10 d3 c10 (by decide +kernel)
  have t5 : a 5 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 5 ≠ 11 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 11 d3 c10 (by decide +kernel)
  have t6 : a 5 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 5 ≠ 12 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 12 d3 c10 (by decide +kernel)
  have t7 : a 5 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 5 ≠ 13 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 13 d3 c10 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := remove (a 5) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 5 ≠ 14 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 14 d3 c10 (by decide +kernel)
  have t9 : a 5 ∈ [0,1,15,16,17,18,19,20,21,22,23] := remove (a 5) 14 [0,1,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 5 ≠ 15 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 15 d3 c10 (by decide +kernel)
  have t10 : a 5 ∈ [0,1,16,17,18,19,20,21,22,23] := remove (a 5) 15 [0,1,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 5 ≠ 16 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 16 d3 c10 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,17,18,19,20,21,22,23] := remove (a 5) 16 [0,1,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 5 ≠ 17 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 17 d3 c10 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,18,19,20,21,22,23] := remove (a 5) 17 [0,1,17,18,19,20,21,22,23] t11 b12
  have b13 : a 5 ≠ 20 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 20 d3 c10 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,18,19,21,22,23] := remove (a 5) 20 [0,1,18,19,20,21,22,23] t12 b13
  have b14 : a 5 ≠ 21 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 21 d3 c10 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,18,19,22,23] := remove (a 5) 21 [0,1,18,19,21,22,23] t13 b14
  have b15 : a 5 ≠ 22 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 22 d3 c10 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,18,19,23] := remove (a 5) 22 [0,1,18,19,22,23] t14 b15
  exact t15

theorem chunk2 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,18,19,23])
    (d3 : a 3 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,3])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c10 : edge r10 (a 3) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 4) (a 18)=true)
    : a 5 ∈ [0,1,18,19] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0,3] ∧ a 18 ∈ [0,1,2,7,8,9,10,11] := by
  have b0 : a 5 ≠ 23 := exclude [0] (fun u v => edge r10 v u) (a 5) (a 3) 23 d3 c10 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,18,19] := remove (a 5) 23 [0,1,18,19,23] d5 b0
  have b1 : a 6 ≠ 1 := exclude [0,3] (fun u v => edge r13 v u) (a 6) (a 4) 1 d4 c13 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b1
  have b2 : a 6 ≠ 2 := exclude [0,3] (fun u v => edge r13 v u) (a 6) (a 4) 2 d4 c13 (by decide +kernel)
  have t2 : a 6 ∈ [0,3] := remove (a 6) 2 [0,2,3] t1 b2
  have b3 : a 6 ≠ 3 := exclude [0,3] (fun u v => edge r13 v u) (a 6) (a 4) 3 d4 c13 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 3 [0,3] t2 b3
  have b4 : a 12 ≠ 1 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 1 d4 c14 (by decide +kernel)
  have t4 : a 12 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9] d12 b4
  have b5 : a 12 ≠ 2 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 2 d4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [0,3,4,5,6,7,8,9] := remove (a 12) 2 [0,2,3,4,5,6,7,8,9] t4 b5
  have b6 : a 12 ≠ 4 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 4 d4 c14 (by decide +kernel)
  have t6 : a 12 ∈ [0,3,5,6,7,8,9] := remove (a 12) 4 [0,3,4,5,6,7,8,9] t5 b6
  have b7 : a 12 ≠ 5 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 5 d4 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0,3,6,7,8,9] := remove (a 12) 5 [0,3,5,6,7,8,9] t6 b7
  have b8 : a 12 ≠ 6 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 6 d4 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0,3,7,8,9] := remove (a 12) 6 [0,3,6,7,8,9] t7 b8
  have b9 : a 12 ≠ 7 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 7 d4 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0,3,8,9] := remove (a 12) 7 [0,3,7,8,9] t8 b9
  have b10 : a 12 ≠ 8 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 8 d4 c14 (by decide +kernel)
  have t10 : a 12 ∈ [0,3,9] := remove (a 12) 8 [0,3,8,9] t9 b10
  have b11 : a 12 ≠ 9 := exclude [0,3] (fun u v => edge r14 v u) (a 12) (a 4) 9 d4 c14 (by decide +kernel)
  have t11 : a 12 ∈ [0,3] := remove (a 12) 9 [0,3,9] t10 b11
  have b12 : a 18 ≠ 3 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 3 d4 c15 (by decide +kernel)
  have t12 : a 18 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 18) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b12
  have b13 : a 18 ≠ 4 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 4 d4 c15 (by decide +kernel)
  have t13 : a 18 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 18) 4 [0,1,2,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 18 ≠ 5 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 5 d4 c15 (by decide +kernel)
  have t14 : a 18 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 18) 5 [0,1,2,5,6,7,8,9,10,11] t13 b14
  have b15 : a 18 ≠ 6 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 6 d4 c15 (by decide +kernel)
  have t15 : a 18 ∈ [0,1,2,7,8,9,10,11] := remove (a 18) 6 [0,1,2,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t3 (And.intro t11 (t15)))

theorem chunk3 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,2,7,8,9,10,11])
    (d4 : a 4 ∈ [0,3])
    (d5 : a 5 ∈ [0,1,18,19])
    (d6 : a 6 ∈ [0])
    (d13 : a 13 ∈ [0,1,2])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c15 : edge r15 (a 4) (a 18)=true)
    (c16 : edge r16 (a 5) (a 6)=true)
    (c17 : edge r17 (a 5) (a 13)=true)
    (c18 : edge r18 (a 5) (a 19)=true)
    : a 18 ∈ [0,1,2] ∧ a 5 ∈ [0,18] ∧ a 13 ∈ [0] ∧ a 19 ∈ [0,8,9,10,11] := by
  have b0 : a 18 ≠ 7 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 7 d4 c15 (by decide +kernel)
  have t0 : a 18 ∈ [0,1,2,8,9,10,11] := remove (a 18) 7 [0,1,2,7,8,9,10,11] d18 b0
  have b1 : a 18 ≠ 8 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 8 d4 c15 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,2,9,10,11] := remove (a 18) 8 [0,1,2,8,9,10,11] t0 b1
  have b2 : a 18 ≠ 9 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 9 d4 c15 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,2,10,11] := remove (a 18) 9 [0,1,2,9,10,11] t1 b2
  have b3 : a 18 ≠ 10 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 10 d4 c15 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,2,11] := remove (a 18) 10 [0,1,2,10,11] t2 b3
  have b4 : a 18 ≠ 11 := exclude [0,3] (fun u v => edge r15 v u) (a 18) (a 4) 11 d4 c15 (by decide +kernel)
  have t4 : a 18 ∈ [0,1,2] := remove (a 18) 11 [0,1,2,11] t3 b4
  have b5 : a 5 ≠ 1 := exclude [0] (edge r16) (a 5) (a 6) 1 d6 c16 (by decide +kernel)
  have t5 : a 5 ∈ [0,18,19] := remove (a 5) 1 [0,1,18,19] d5 b5
  have b6 : a 5 ≠ 19 := exclude [0] (edge r16) (a 5) (a 6) 19 d6 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0,18] := remove (a 5) 19 [0,18,19] t5 b6
  have b7 : a 13 ≠ 1 := exclude [0,18] (fun u v => edge r17 v u) (a 13) (a 5) 1 t6 c17 (by decide +kernel)
  have t7 : a 13 ∈ [0,2] := remove (a 13) 1 [0,1,2] d13 b7
  have b8 : a 13 ≠ 2 := exclude [0,18] (fun u v => edge r17 v u) (a 13) (a 5) 2 t6 c17 (by decide +kernel)
  have t8 : a 13 ∈ [0] := remove (a 13) 2 [0,2] t7 b8
  have b9 : a 19 ≠ 1 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 1 t6 c18 (by decide +kernel)
  have t9 : a 19 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b9
  have b10 : a 19 ≠ 2 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 2 t6 c18 (by decide +kernel)
  have t10 : a 19 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,2,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 19 ≠ 3 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 3 t6 c18 (by decide +kernel)
  have t11 : a 19 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 19 ≠ 4 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 4 t6 c18 (by decide +kernel)
  have t12 : a 19 ∈ [0,5,6,7,8,9,10,11] := remove (a 19) 4 [0,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 19 ≠ 5 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 5 t6 c18 (by decide +kernel)
  have t13 : a 19 ∈ [0,6,7,8,9,10,11] := remove (a 19) 5 [0,5,6,7,8,9,10,11] t12 b13
  have b14 : a 19 ≠ 6 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 6 t6 c18 (by decide +kernel)
  have t14 : a 19 ∈ [0,7,8,9,10,11] := remove (a 19) 6 [0,6,7,8,9,10,11] t13 b14
  have b15 : a 19 ≠ 7 := exclude [0,18] (fun u v => edge r18 v u) (a 19) (a 5) 7 t6 c18 (by decide +kernel)
  have t15 : a 19 ∈ [0,8,9,10,11] := remove (a 19) 7 [0,7,8,9,10,11] t14 b15
  exact And.intro t4 (And.intro t6 (And.intro t8 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_215
