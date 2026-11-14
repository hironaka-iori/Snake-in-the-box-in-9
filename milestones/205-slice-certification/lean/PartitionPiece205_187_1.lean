import PartitionData205_187
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,8])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    : a 6 ∈ [0,8] ∧ a 10 ∈ [0,2,3,5,7,8,9,10,11] := by
  have b0 : a 6 ≠ 11 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 11 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 11 [0,8,11,12,13,14,15,16,17,18,19,20,21,22,23] d6 b0
  have b1 : a 6 ≠ 12 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 12 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,8,13,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 12 [0,8,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 6 ≠ 13 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 13 d2 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,8,14,15,16,17,18,19,20,21,22,23] := remove (a 6) 13 [0,8,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 6 ≠ 14 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 14 d2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,8,15,16,17,18,19,20,21,22,23] := remove (a 6) 14 [0,8,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 6 ≠ 15 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 15 d2 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,8,16,17,18,19,20,21,22,23] := remove (a 6) 15 [0,8,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 6 ≠ 16 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 16 d2 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0,8,17,18,19,20,21,22,23] := remove (a 6) 16 [0,8,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 6 ≠ 17 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 17 d2 c10 (by decide +kernel)
  have t6 : a 6 ∈ [0,8,18,19,20,21,22,23] := remove (a 6) 17 [0,8,17,18,19,20,21,22,23] t5 b6
  have b7 : a 6 ≠ 18 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 18 d2 c10 (by decide +kernel)
  have t7 : a 6 ∈ [0,8,19,20,21,22,23] := remove (a 6) 18 [0,8,18,19,20,21,22,23] t6 b7
  have b8 : a 6 ≠ 19 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 19 d2 c10 (by decide +kernel)
  have t8 : a 6 ∈ [0,8,20,21,22,23] := remove (a 6) 19 [0,8,19,20,21,22,23] t7 b8
  have b9 : a 6 ≠ 20 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 20 d2 c10 (by decide +kernel)
  have t9 : a 6 ∈ [0,8,21,22,23] := remove (a 6) 20 [0,8,20,21,22,23] t8 b9
  have b10 : a 6 ≠ 21 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 21 d2 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,8,22,23] := remove (a 6) 21 [0,8,21,22,23] t9 b10
  have b11 : a 6 ≠ 22 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 22 d2 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,8,23] := remove (a 6) 22 [0,8,22,23] t10 b11
  have b12 : a 6 ≠ 23 := exclude [0,8] (fun u v => edge r10 v u) (a 6) (a 2) 23 d2 c10 (by decide +kernel)
  have t12 : a 6 ∈ [0,8] := remove (a 6) 23 [0,8,23] t11 b12
  have b13 : a 10 ≠ 1 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 10) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b13
  have b14 : a 10 ≠ 4 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 10) 4 [0,2,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 10 ≠ 6 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t15 : a 10 ∈ [0,2,3,5,7,8,9,10,11] := remove (a 10) 6 [0,2,3,5,6,7,8,9,10,11] t14 b15
  exact And.intro t12 (t15)

theorem chunk5 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,2,3,5,7,8,9,10,11])
    (d2 : a 2 ∈ [0,8])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 10 ∈ [0,2,3,5] ∧ a 18 ∈ [0,4,12,14,15,16,17,18,19] := by
  have b0 : a 10 ≠ 7 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,2,3,5,8,9,10,11] := remove (a 10) 7 [0,2,3,5,7,8,9,10,11] d10 b0
  have b1 : a 10 ≠ 8 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,2,3,5,9,10,11] := remove (a 10) 8 [0,2,3,5,8,9,10,11] t0 b1
  have b2 : a 10 ≠ 9 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,2,3,5,10,11] := remove (a 10) 9 [0,2,3,5,9,10,11] t1 b2
  have b3 : a 10 ≠ 10 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,2,3,5,11] := remove (a 10) 10 [0,2,3,5,10,11] t2 b3
  have b4 : a 10 ≠ 11 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,2,3,5] := remove (a 10) 11 [0,2,3,5,11] t3 b4
  have b5 : a 18 ≠ 1 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d18 b5
  have b6 : a 18 ≠ 2 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 18 ≠ 3 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 18 ≠ 5 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 18 ≠ 6 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 18 ≠ 7 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,4,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 18 ≠ 8 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,4,9,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 8 [0,4,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 18 ≠ 9 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,4,10,11,12,13,14,15,16,17,18,19] := remove (a 18) 9 [0,4,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 18 ≠ 10 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,4,11,12,13,14,15,16,17,18,19] := remove (a 18) 10 [0,4,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 18 ≠ 11 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,4,12,13,14,15,16,17,18,19] := remove (a 18) 11 [0,4,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 18 ≠ 13 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 13 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,4,12,14,15,16,17,18,19] := remove (a 18) 13 [0,4,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t4 (t15)

theorem chunk6 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,4,12,14,15,16,17,18,19])
    (d2 : a 2 ∈ [0,8])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d3 : a 3 ∈ [0,5,6,11])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 18 ∈ [0,4,12,14] ∧ a 11 ∈ [0,5,6,9] ∧ a 19 ∈ [0,5,6,8,9] := by
  have b0 : a 18 ≠ 15 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 15 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,4,12,14,16,17,18,19] := remove (a 18) 15 [0,4,12,14,15,16,17,18,19] d18 b0
  have b1 : a 18 ≠ 16 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,4,12,14,17,18,19] := remove (a 18) 16 [0,4,12,14,16,17,18,19] t0 b1
  have b2 : a 18 ≠ 17 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,4,12,14,18,19] := remove (a 18) 17 [0,4,12,14,17,18,19] t1 b2
  have b3 : a 18 ≠ 18 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 18 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,4,12,14,19] := remove (a 18) 18 [0,4,12,14,18,19] t2 b3
  have b4 : a 18 ≠ 19 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 19 d2 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,4,12,14] := remove (a 18) 19 [0,4,12,14,19] t3 b4
  have b5 : a 11 ≠ 1 := exclude [0,5,6,11] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0,5,6,11] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,3,4,5,6,7,8,9] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9] t5 b6
  have b7 : a 11 ≠ 3 := exclude [0,5,6,11] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,4,5,6,7,8,9] := remove (a 11) 3 [0,3,4,5,6,7,8,9] t6 b7
  have b8 : a 11 ≠ 4 := exclude [0,5,6,11] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,5,6,7,8,9] := remove (a 11) 4 [0,4,5,6,7,8,9] t7 b8
  have b9 : a 11 ≠ 7 := exclude [0,5,6,11] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,5,6,8,9] := remove (a 11) 7 [0,5,6,7,8,9] t8 b9
  have b10 : a 11 ≠ 8 := exclude [0,5,6,11] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,5,6,9] := remove (a 11) 8 [0,5,6,8,9] t9 b10
  have b11 : a 19 ≠ 1 := exclude [0,5,6,11] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t11 : a 19 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9] d19 b11
  have b12 : a 19 ≠ 2 := exclude [0,5,6,11] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,3,4,5,6,7,8,9] := remove (a 19) 2 [0,2,3,4,5,6,7,8,9] t11 b12
  have b13 : a 19 ≠ 3 := exclude [0,5,6,11] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t13 : a 19 ∈ [0,4,5,6,7,8,9] := remove (a 19) 3 [0,3,4,5,6,7,8,9] t12 b13
  have b14 : a 19 ≠ 4 := exclude [0,5,6,11] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,5,6,7,8,9] := remove (a 19) 4 [0,4,5,6,7,8,9] t13 b14
  have b15 : a 19 ≠ 7 := exclude [0,5,6,11] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,5,6,8,9] := remove (a 19) 7 [0,5,6,7,8,9] t14 b15
  exact And.intro t4 (And.intro t10 (t15))

theorem chunk7 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,5,6,8,9])
    (d3 : a 3 ∈ [0,5,6,11])
    (d5 : a 5 ∈ [0,4,8,10,11,19,20,22])
    (d4 : a 4 ∈ [0,1,9,10])
    (d6 : a 6 ∈ [0,8])
    (d12 : a 12 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    : a 19 ∈ [0,5,6,9] ∧ a 5 ∈ [0,4,20,22] ∧ a 4 ∈ [0,9] ∧ a 12 ∈ [0,2] ∧ a 20 ∈ [0,1,2,9,10,11] ∧ a 13 ∈ [0,1,3,4,5,6,7] := by
  have b0 : a 19 ≠ 8 := exclude [0,5,6,11] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,5,6,9] := remove (a 19) 8 [0,5,6,8,9] d19 b0
  have b1 : a 5 ≠ 8 := exclude [0,1,9,10] (fun u v => edge r16 v u) (a 5) (a 4) 8 d4 c16 (by decide +kernel)
  have t1 : a 5 ∈ [0,4,10,11,19,20,22] := remove (a 5) 8 [0,4,8,10,11,19,20,22] d5 b1
  have b2 : a 5 ≠ 10 := exclude [0,1,9,10] (fun u v => edge r16 v u) (a 5) (a 4) 10 d4 c16 (by decide +kernel)
  have t2 : a 5 ∈ [0,4,11,19,20,22] := remove (a 5) 10 [0,4,10,11,19,20,22] t1 b2
  have b3 : a 5 ≠ 11 := exclude [0,1,9,10] (fun u v => edge r16 v u) (a 5) (a 4) 11 d4 c16 (by decide +kernel)
  have t3 : a 5 ∈ [0,4,19,20,22] := remove (a 5) 11 [0,4,11,19,20,22] t2 b3
  have b4 : a 5 ≠ 19 := exclude [0,1,9,10] (fun u v => edge r16 v u) (a 5) (a 4) 19 d4 c16 (by decide +kernel)
  have t4 : a 5 ∈ [0,4,20,22] := remove (a 5) 19 [0,4,19,20,22] t3 b4
  have b5 : a 4 ≠ 1 := exclude [0,8] (edge r17) (a 4) (a 6) 1 d6 c17 (by decide +kernel)
  have t5 : a 4 ∈ [0,9,10] := remove (a 4) 1 [0,1,9,10] d4 b5
  have b6 : a 4 ≠ 10 := exclude [0,8] (edge r17) (a 4) (a 6) 10 d6 c17 (by decide +kernel)
  have t6 : a 4 ∈ [0,9] := remove (a 4) 10 [0,9,10] t5 b6
  have b7 : a 12 ≠ 1 := exclude [0,9] (fun u v => edge r18 v u) (a 12) (a 4) 1 t6 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b7
  have b8 : a 12 ≠ 3 := exclude [0,9] (fun u v => edge r18 v u) (a 12) (a 4) 3 t6 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t7 b8
  have b9 : a 20 ≠ 3 := exclude [0,9] (fun u v => edge r19 v u) (a 20) (a 4) 3 t6 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b9
  have b10 : a 20 ≠ 4 := exclude [0,9] (fun u v => edge r19 v u) (a 20) (a 4) 4 t6 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 20) 4 [0,1,2,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 20 ≠ 5 := exclude [0,9] (fun u v => edge r19 v u) (a 20) (a 4) 5 t6 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 20) 5 [0,1,2,5,6,7,8,9,10,11] t10 b11
  have b12 : a 20 ≠ 6 := exclude [0,9] (fun u v => edge r19 v u) (a 20) (a 4) 6 t6 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,2,7,8,9,10,11] := remove (a 20) 6 [0,1,2,6,7,8,9,10,11] t11 b12
  have b13 : a 20 ≠ 7 := exclude [0,9] (fun u v => edge r19 v u) (a 20) (a 4) 7 t6 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,2,8,9,10,11] := remove (a 20) 7 [0,1,2,7,8,9,10,11] t12 b13
  have b14 : a 20 ≠ 8 := exclude [0,9] (fun u v => edge r19 v u) (a 20) (a 4) 8 t6 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,2,9,10,11] := remove (a 20) 8 [0,1,2,8,9,10,11] t13 b14
  have b15 : a 13 ≠ 2 := exclude [0,4,20,22] (fun u v => edge r21 v u) (a 13) (a 5) 2 t4 c21 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,3,4,5,6,7] := remove (a 13) 2 [0,1,2,3,4,5,6,7] d13 b15
  exact And.intro t0 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t14 (t15)))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_187
