import PartitionData205_201
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,8])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 10 ∈ [0,1,4,5] ∧ a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 10 ≠ 9 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b0
  have b1 : a 10 ≠ 10 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 10 [0,1,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 10 ≠ 11 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 11 [0,1,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 10 ≠ 12 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 12 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 12 [0,1,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 10 ≠ 13 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 13 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 13 [0,1,4,5,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 10 ≠ 14 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 14 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,4,5,15,16,17,18,19,20,21,22,23] := remove (a 10) 14 [0,1,4,5,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 10 ≠ 15 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 15 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,4,5,16,17,18,19,20,21,22,23] := remove (a 10) 15 [0,1,4,5,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 10 ≠ 16 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 16 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,4,5,17,18,19,20,21,22,23] := remove (a 10) 16 [0,1,4,5,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 10 ≠ 17 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 17 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,4,5,18,19,20,21,22,23] := remove (a 10) 17 [0,1,4,5,17,18,19,20,21,22,23] t7 b8
  have b9 : a 10 ≠ 18 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 18 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,4,5,19,20,21,22,23] := remove (a 10) 18 [0,1,4,5,18,19,20,21,22,23] t8 b9
  have b10 : a 10 ≠ 19 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 19 d2 c11 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,4,5,20,21,22,23] := remove (a 10) 19 [0,1,4,5,19,20,21,22,23] t9 b10
  have b11 : a 10 ≠ 20 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 20 d2 c11 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,4,5,21,22,23] := remove (a 10) 20 [0,1,4,5,20,21,22,23] t10 b11
  have b12 : a 10 ≠ 21 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 21 d2 c11 (by decide +kernel)
  have t12 : a 10 ∈ [0,1,4,5,22,23] := remove (a 10) 21 [0,1,4,5,21,22,23] t11 b12
  have b13 : a 10 ≠ 22 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 22 d2 c11 (by decide +kernel)
  have t13 : a 10 ∈ [0,1,4,5,23] := remove (a 10) 22 [0,1,4,5,22,23] t12 b13
  have b14 : a 10 ≠ 23 := exclude [0,8] (fun u v => edge r11 v u) (a 10) (a 2) 23 d2 c11 (by decide +kernel)
  have t14 : a 10 ∈ [0,1,4,5] := remove (a 10) 23 [0,1,4,5,23] t13 b14
  have b15 : a 18 ≠ 1 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b15
  exact And.intro t14 (t15)

theorem chunk5 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0,8])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 18 ∈ [0,8] ∧ a 7 ∈ [0,1,4,5] ∧ a 11 ∈ [0,1,4,5,6,7,10,11,12,13,15,16,17] := by
  have b0 : a 18 ≠ 2 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 18) 2 [0,2,3,4,5,6,7,8,9,10,11] d18 b0
  have b1 : a 18 ≠ 3 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 18) 3 [0,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 18 ≠ 4 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,5,6,7,8,9,10,11] := remove (a 18) 4 [0,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 18 ≠ 5 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,6,7,8,9,10,11] := remove (a 18) 5 [0,5,6,7,8,9,10,11] t2 b3
  have b4 : a 18 ≠ 6 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,7,8,9,10,11] := remove (a 18) 6 [0,6,7,8,9,10,11] t3 b4
  have b5 : a 18 ≠ 7 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,8,9,10,11] := remove (a 18) 7 [0,7,8,9,10,11] t4 b5
  have b6 : a 18 ≠ 9 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,8,10,11] := remove (a 18) 9 [0,8,9,10,11] t5 b6
  have b7 : a 18 ≠ 10 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,8,11] := remove (a 18) 10 [0,8,10,11] t6 b7
  have b8 : a 18 ≠ 11 := exclude [0,8] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,8] := remove (a 18) 11 [0,8,11] t7 b8
  have b9 : a 7 ≠ 2 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t9 : a 7 ∈ [0,1,3,4,5] := remove (a 7) 2 [0,1,2,3,4,5] d7 b9
  have b10 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 3 d3 c13 (by decide +kernel)
  have t10 : a 7 ∈ [0,1,4,5] := remove (a 7) 3 [0,1,3,4,5] t9 b10
  have b11 : a 11 ≠ 2 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d11 b11
  have b12 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 11) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 11 ≠ 8 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17] := remove (a 11) 8 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 11 ≠ 9 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 9 d3 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,1,4,5,6,7,10,11,12,13,14,15,16,17] := remove (a 11) 9 [0,1,4,5,6,7,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 11 ≠ 14 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 14 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,1,4,5,6,7,10,11,12,13,15,16,17] := remove (a 11) 14 [0,1,4,5,6,7,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t8 (And.intro t10 (t15))

theorem chunk6 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,4,5,6,7,10,11,12,13,15,16,17])
    (d3 : a 3 ∈ [0,2])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 11 ∈ [0,1,4,5,6,7,10,11,12,13,16,17] ∧ a 19 ∈ [0,1,3,5,6,7,8,9,11,13,15,17] ∧ a 12 ∈ [0,1,3,4,5,7,8,9,11,13,15,17] ∧ a 20 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 11 ≠ 15 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 15 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,1,4,5,6,7,10,11,12,13,16,17] := remove (a 11) 15 [0,1,4,5,6,7,10,11,12,13,15,16,17] d11 b0
  have b1 : a 19 ≠ 2 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d19 b1
  have b2 : a 19 ≠ 4 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 4 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 19 ≠ 10 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 10 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,3,5,6,7,8,9,11,12,13,14,15,16,17] := remove (a 19) 10 [0,1,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 19 ≠ 12 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 12 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,3,5,6,7,8,9,11,13,14,15,16,17] := remove (a 19) 12 [0,1,3,5,6,7,8,9,11,12,13,14,15,16,17] t3 b4
  have b5 : a 19 ≠ 14 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 14 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,1,3,5,6,7,8,9,11,13,15,16,17] := remove (a 19) 14 [0,1,3,5,6,7,8,9,11,13,14,15,16,17] t4 b5
  have b6 : a 19 ≠ 16 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 16 d3 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0,1,3,5,6,7,8,9,11,13,15,17] := remove (a 19) 16 [0,1,3,5,6,7,8,9,11,13,15,16,17] t5 b6
  have b7 : a 12 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d12 b7
  have b8 : a 12 ≠ 6 := exclude [0,1,2,3] (fun u v => edge r18 v u) (a 12) (a 4) 6 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 12) 6 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 12 ≠ 10 := exclude [0,1,2,3] (fun u v => edge r18 v u) (a 12) (a 4) 10 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,3,4,5,7,8,9,11,12,13,14,15,16,17] := remove (a 12) 10 [0,1,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 12 ≠ 12 := exclude [0,1,2,3] (fun u v => edge r18 v u) (a 12) (a 4) 12 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,3,4,5,7,8,9,11,13,14,15,16,17] := remove (a 12) 12 [0,1,3,4,5,7,8,9,11,12,13,14,15,16,17] t9 b10
  have b11 : a 12 ≠ 14 := exclude [0,1,2,3] (fun u v => edge r18 v u) (a 12) (a 4) 14 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,3,4,5,7,8,9,11,13,15,16,17] := remove (a 12) 14 [0,1,3,4,5,7,8,9,11,13,14,15,16,17] t10 b11
  have b12 : a 12 ≠ 16 := exclude [0,1,2,3] (fun u v => edge r18 v u) (a 12) (a 4) 16 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,3,4,5,7,8,9,11,13,15,17] := remove (a 12) 16 [0,1,3,4,5,7,8,9,11,13,15,16,17] t11 b12
  have b13 : a 20 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d20 b13
  have b14 : a 20 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 20 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t6 (And.intro t12 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d5 : a 5 ∈ [0,2,4,5])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,1,4,5])
    (d6 : a 6 ∈ [0,5])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    : a 20 ∈ [0,1,6,7,8,9,12,13] ∧ a 13 ∈ [0,2,4] ∧ a 21 ∈ [0,2,3,4,5,6,8] ∧ a 7 ∈ [0,4,5] := by
  have b0 : a 20 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 20) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] d20 b0
  have b1 : a 20 ≠ 10 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,6,7,8,9,11,12,13,14,15,16,17] := remove (a 20) 10 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 20 ≠ 11 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,6,7,8,9,12,13,14,15,16,17] := remove (a 20) 11 [0,1,6,7,8,9,11,12,13,14,15,16,17] t1 b2
  have b3 : a 20 ≠ 14 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 14 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,6,7,8,9,12,13,15,16,17] := remove (a 20) 14 [0,1,6,7,8,9,12,13,14,15,16,17] t2 b3
  have b4 : a 20 ≠ 15 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 15 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,6,7,8,9,12,13,16,17] := remove (a 20) 15 [0,1,6,7,8,9,12,13,15,16,17] t3 b4
  have b5 : a 20 ≠ 16 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 16 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,6,7,8,9,12,13,17] := remove (a 20) 16 [0,1,6,7,8,9,12,13,16,17] t4 b5
  have b6 : a 20 ≠ 17 := exclude [0,1,2,3] (fun u v => edge r19 v u) (a 20) (a 4) 17 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,6,7,8,9,12,13] := remove (a 20) 17 [0,1,6,7,8,9,12,13,17] t5 b6
  have b7 : a 13 ≠ 1 := exclude [0,2,4,5] (fun u v => edge r21 v u) (a 13) (a 5) 1 d5 c21 (by decide +kernel)
  have t7 : a 13 ∈ [0,2,3,4,5,6,7,8] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8] d13 b7
  have b8 : a 13 ≠ 3 := exclude [0,2,4,5] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,4,5,6,7,8] := remove (a 13) 3 [0,2,3,4,5,6,7,8] t7 b8
  have b9 : a 13 ≠ 5 := exclude [0,2,4,5] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,2,4,6,7,8] := remove (a 13) 5 [0,2,4,5,6,7,8] t8 b9
  have b10 : a 13 ≠ 6 := exclude [0,2,4,5] (fun u v => edge r21 v u) (a 13) (a 5) 6 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,2,4,7,8] := remove (a 13) 6 [0,2,4,6,7,8] t9 b10
  have b11 : a 13 ≠ 7 := exclude [0,2,4,5] (fun u v => edge r21 v u) (a 13) (a 5) 7 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,2,4,8] := remove (a 13) 7 [0,2,4,7,8] t10 b11
  have b12 : a 13 ≠ 8 := exclude [0,2,4,5] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,2,4] := remove (a 13) 8 [0,2,4,8] t11 b12
  have b13 : a 21 ≠ 1 := exclude [0,2,4,5] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,2,3,4,5,6,7,8] := remove (a 21) 1 [0,1,2,3,4,5,6,7,8] d21 b13
  have b14 : a 21 ≠ 7 := exclude [0,2,4,5] (fun u v => edge r22 v u) (a 21) (a 5) 7 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,2,3,4,5,6,8] := remove (a 21) 7 [0,2,3,4,5,6,7,8] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0,5] (fun u v => edge r23 v u) (a 7) (a 6) 1 d6 c23 (by decide +kernel)
  have t15 : a 7 ∈ [0,4,5] := remove (a 7) 1 [0,1,4,5] d7 b15
  exact And.intro t6 (And.intro t12 (And.intro t14 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_201
