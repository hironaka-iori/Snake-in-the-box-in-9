import PartitionData205_158
namespace PartitionCover205_158
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0])
    (d5 : a 5 ∈ [0,8])
    (d4 : a 4 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (c9 : edge r9 (a 2) (a 10)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 10 ∈ [0,1,2,3] ∧ a 5 ∈ [0] ∧ a 12 ∈ [0,8,10,11,12,13] := by
  have b0 : a 10 ≠ 5 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 5 d2 c9 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 10) 5 [0,1,2,3,5,6,7,8,9,10,11] d10 b0
  have b1 : a 10 ≠ 6 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 6 d2 c9 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 10) 6 [0,1,2,3,6,7,8,9,10,11] t0 b1
  have b2 : a 10 ≠ 7 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 7 d2 c9 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,2,3,8,9,10,11] := remove (a 10) 7 [0,1,2,3,7,8,9,10,11] t1 b2
  have b3 : a 10 ≠ 8 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 8 d2 c9 (by decide +kernel)
  have t3 : a 10 ∈ [0,1,2,3,9,10,11] := remove (a 10) 8 [0,1,2,3,8,9,10,11] t2 b3
  have b4 : a 10 ≠ 9 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 9 d2 c9 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,2,3,10,11] := remove (a 10) 9 [0,1,2,3,9,10,11] t3 b4
  have b5 : a 10 ≠ 10 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 10 d2 c9 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,2,3,11] := remove (a 10) 10 [0,1,2,3,10,11] t4 b5
  have b6 : a 10 ≠ 11 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 11 d2 c9 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,2,3] := remove (a 10) 11 [0,1,2,3,11] t5 b6
  have b7 : a 5 ≠ 8 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 8 d4 c12 (by decide +kernel)
  have t7 : a 5 ∈ [0] := remove (a 5) 8 [0,8] d5 b7
  have b8 : a 12 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 1 d4 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d12 b8
  have b9 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 d4 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 12) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t8 b9
  have b10 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 d4 c14 (by decide +kernel)
  have t10 : a 12 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 12) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t9 b10
  have b11 : a 12 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 4 d4 c14 (by decide +kernel)
  have t11 : a 12 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 12) 4 [0,4,5,6,7,8,9,10,11,12,13] t10 b11
  have b12 : a 12 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 5 d4 c14 (by decide +kernel)
  have t12 : a 12 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 12) 5 [0,5,6,7,8,9,10,11,12,13] t11 b12
  have b13 : a 12 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 6 d4 c14 (by decide +kernel)
  have t13 : a 12 ∈ [0,7,8,9,10,11,12,13] := remove (a 12) 6 [0,6,7,8,9,10,11,12,13] t12 b13
  have b14 : a 12 ≠ 7 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 7 d4 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,8,9,10,11,12,13] := remove (a 12) 7 [0,7,8,9,10,11,12,13] t13 b14
  have b15 : a 12 ≠ 9 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 9 d4 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,8,10,11,12,13] := remove (a 12) 9 [0,8,9,10,11,12,13] t14 b15
  exact And.intro t6 (And.intro t7 (t15))

theorem chunk5 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,8,10,11,12,13])
    (d4 : a 4 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d5 : a 5 ∈ [0])
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    : a 12 ∈ [0,8] ∧ a 7 ∈ [0,13] := by
  have b0 : a 12 ≠ 10 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 10 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,8,11,12,13] := remove (a 12) 10 [0,8,10,11,12,13] d12 b0
  have b1 : a 12 ≠ 11 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 11 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,8,12,13] := remove (a 12) 11 [0,8,11,12,13] t0 b1
  have b2 : a 12 ≠ 12 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 12 d4 c14 (by decide +kernel)
  have t2 : a 12 ∈ [0,8,13] := remove (a 12) 12 [0,8,12,13] t1 b2
  have b3 : a 12 ≠ 13 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 13 d4 c14 (by decide +kernel)
  have t3 : a 12 ∈ [0,8] := remove (a 12) 13 [0,8,13] t2 b3
  have b4 : a 7 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 1 d5 c15 (by decide +kernel)
  have t4 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d7 b4
  have b5 : a 7 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 2 d5 c15 (by decide +kernel)
  have t5 : a 7 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 7) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t4 b5
  have b6 : a 7 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 3 d5 c15 (by decide +kernel)
  have t6 : a 7 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 7) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t5 b6
  have b7 : a 7 ≠ 4 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 4 d5 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 7) 4 [0,4,5,6,7,8,9,10,11,12,13] t6 b7
  have b8 : a 7 ≠ 5 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 5 d5 c15 (by decide +kernel)
  have t8 : a 7 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 7) 5 [0,5,6,7,8,9,10,11,12,13] t7 b8
  have b9 : a 7 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 6 d5 c15 (by decide +kernel)
  have t9 : a 7 ∈ [0,7,8,9,10,11,12,13] := remove (a 7) 6 [0,6,7,8,9,10,11,12,13] t8 b9
  have b10 : a 7 ≠ 7 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 7 d5 c15 (by decide +kernel)
  have t10 : a 7 ∈ [0,8,9,10,11,12,13] := remove (a 7) 7 [0,7,8,9,10,11,12,13] t9 b10
  have b11 : a 7 ≠ 8 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 8 d5 c15 (by decide +kernel)
  have t11 : a 7 ∈ [0,9,10,11,12,13] := remove (a 7) 8 [0,8,9,10,11,12,13] t10 b11
  have b12 : a 7 ≠ 9 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 9 d5 c15 (by decide +kernel)
  have t12 : a 7 ∈ [0,10,11,12,13] := remove (a 7) 9 [0,9,10,11,12,13] t11 b12
  have b13 : a 7 ≠ 10 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 10 d5 c15 (by decide +kernel)
  have t13 : a 7 ∈ [0,11,12,13] := remove (a 7) 10 [0,10,11,12,13] t12 b13
  have b14 : a 7 ≠ 11 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 11 d5 c15 (by decide +kernel)
  have t14 : a 7 ∈ [0,12,13] := remove (a 7) 11 [0,11,12,13] t13 b14
  have b15 : a 7 ≠ 12 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 12 d5 c15 (by decide +kernel)
  have t15 : a 7 ∈ [0,13] := remove (a 7) 12 [0,12,13] t14 b15
  exact And.intro t3 (t15)

theorem chunk6 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,13])
    (d5 : a 5 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d6 : a 6 ∈ [0])
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    : a 7 ∈ [0] ∧ a 13 ∈ [0,8] ∧ a 14 ∈ [0,4,5,6,7,8,9,10,11,12,13] := by
  have b0 : a 7 ≠ 13 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 5) 13 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0] := remove (a 7) 13 [0,13] d7 b0
  have b1 : a 13 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 1 d5 c16 (by decide +kernel)
  have t1 : a 13 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d13 b1
  have b2 : a 13 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t2 : a 13 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 13) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t1 b2
  have b3 : a 13 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t3 : a 13 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 13) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t2 b3
  have b4 : a 13 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 13) 4 [0,4,5,6,7,8,9,10,11,12,13] t3 b4
  have b5 : a 13 ≠ 5 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 13) 5 [0,5,6,7,8,9,10,11,12,13] t4 b5
  have b6 : a 13 ≠ 6 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,7,8,9,10,11,12,13] := remove (a 13) 6 [0,6,7,8,9,10,11,12,13] t5 b6
  have b7 : a 13 ≠ 7 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,8,9,10,11,12,13] := remove (a 13) 7 [0,7,8,9,10,11,12,13] t6 b7
  have b8 : a 13 ≠ 9 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 9 d5 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,8,10,11,12,13] := remove (a 13) 9 [0,8,9,10,11,12,13] t7 b8
  have b9 : a 13 ≠ 10 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 10 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,8,11,12,13] := remove (a 13) 10 [0,8,10,11,12,13] t8 b9
  have b10 : a 13 ≠ 11 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 11 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,8,12,13] := remove (a 13) 11 [0,8,11,12,13] t9 b10
  have b11 : a 13 ≠ 12 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 12 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,8,13] := remove (a 13) 12 [0,8,12,13] t10 b11
  have b12 : a 13 ≠ 13 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 13 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,8] := remove (a 13) 13 [0,8,13] t11 b12
  have b13 : a 14 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 1 d6 c18 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d14 b13
  have b14 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 d6 c18 (by decide +kernel)
  have t14 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t13 b14
  have b15 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 d6 c18 (by decide +kernel)
  have t15 : a 14 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t14 b15
  exact And.intro t0 (And.intro t12 (t15))

theorem chunk7 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,4,5,6,7,8,9,10,11,12,13])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d7 : a 7 ∈ [0])
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 14 ∈ [0] ∧ a 15 ∈ [0,7,8,9,10,11,12,13] := by
  have b0 : a 14 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 4 d6 c18 (by decide +kernel)
  have t0 : a 14 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 14) 4 [0,4,5,6,7,8,9,10,11,12,13] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 5 d6 c18 (by decide +kernel)
  have t1 : a 14 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 14) 5 [0,5,6,7,8,9,10,11,12,13] t0 b1
  have b2 : a 14 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 6 d6 c18 (by decide +kernel)
  have t2 : a 14 ∈ [0,7,8,9,10,11,12,13] := remove (a 14) 6 [0,6,7,8,9,10,11,12,13] t1 b2
  have b3 : a 14 ≠ 7 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 7 d6 c18 (by decide +kernel)
  have t3 : a 14 ∈ [0,8,9,10,11,12,13] := remove (a 14) 7 [0,7,8,9,10,11,12,13] t2 b3
  have b4 : a 14 ≠ 8 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 8 d6 c18 (by decide +kernel)
  have t4 : a 14 ∈ [0,9,10,11,12,13] := remove (a 14) 8 [0,8,9,10,11,12,13] t3 b4
  have b5 : a 14 ≠ 9 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 9 d6 c18 (by decide +kernel)
  have t5 : a 14 ∈ [0,10,11,12,13] := remove (a 14) 9 [0,9,10,11,12,13] t4 b5
  have b6 : a 14 ≠ 10 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 10 d6 c18 (by decide +kernel)
  have t6 : a 14 ∈ [0,11,12,13] := remove (a 14) 10 [0,10,11,12,13] t5 b6
  have b7 : a 14 ≠ 11 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 11 d6 c18 (by decide +kernel)
  have t7 : a 14 ∈ [0,12,13] := remove (a 14) 11 [0,11,12,13] t6 b7
  have b8 : a 14 ≠ 12 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 12 d6 c18 (by decide +kernel)
  have t8 : a 14 ∈ [0,13] := remove (a 14) 12 [0,12,13] t7 b8
  have b9 : a 14 ≠ 13 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 13 d6 c18 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 13 [0,13] t8 b9
  have b10 : a 15 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 1 d7 c19 (by decide +kernel)
  have t10 : a 15 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13] := remove (a 15) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d15 b10
  have b11 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t11 : a 15 ∈ [0,3,4,5,6,7,8,9,10,11,12,13] := remove (a 15) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13] t10 b11
  have b12 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t12 : a 15 ∈ [0,4,5,6,7,8,9,10,11,12,13] := remove (a 15) 3 [0,3,4,5,6,7,8,9,10,11,12,13] t11 b12
  have b13 : a 15 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 4 d7 c19 (by decide +kernel)
  have t13 : a 15 ∈ [0,5,6,7,8,9,10,11,12,13] := remove (a 15) 4 [0,4,5,6,7,8,9,10,11,12,13] t12 b13
  have b14 : a 15 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,6,7,8,9,10,11,12,13] := remove (a 15) 5 [0,5,6,7,8,9,10,11,12,13] t13 b14
  have b15 : a 15 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 6 d7 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,7,8,9,10,11,12,13] := remove (a 15) 6 [0,6,7,8,9,10,11,12,13] t14 b15
  exact And.intro t9 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_158
