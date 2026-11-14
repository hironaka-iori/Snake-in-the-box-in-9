import PartitionData205_186
namespace PartitionCover205_186
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,3,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,11])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 10 ∈ [0,3,6,11,12,14,15,18,21,23] ∧ a 18 ∈ [0,3,7,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 10 ≠ 10 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,3,6,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 10 [0,3,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d10 b0
  have b1 : a 10 ≠ 13 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 13 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,3,6,11,12,14,15,16,17,18,19,20,21,22,23] := remove (a 10) 13 [0,3,6,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 10 ≠ 16 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 16 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,3,6,11,12,14,15,17,18,19,20,21,22,23] := remove (a 10) 16 [0,3,6,11,12,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 10 ≠ 17 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 17 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,3,6,11,12,14,15,18,19,20,21,22,23] := remove (a 10) 17 [0,3,6,11,12,14,15,17,18,19,20,21,22,23] t2 b3
  have b4 : a 10 ≠ 19 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 19 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,3,6,11,12,14,15,18,20,21,22,23] := remove (a 10) 19 [0,3,6,11,12,14,15,18,19,20,21,22,23] t3 b4
  have b5 : a 10 ≠ 20 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 20 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,3,6,11,12,14,15,18,21,22,23] := remove (a 10) 20 [0,3,6,11,12,14,15,18,20,21,22,23] t4 b5
  have b6 : a 10 ≠ 22 := exclude [0,11] (fun u v => edge r11 v u) (a 10) (a 2) 22 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,3,6,11,12,14,15,18,21,23] := remove (a 10) 22 [0,3,6,11,12,14,15,18,21,22,23] t5 b6
  have b7 : a 18 ≠ 1 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d18 b7
  have b8 : a 18 ≠ 2 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 18 ≠ 4 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 4 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 18 ≠ 5 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 5 [0,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 18 ≠ 6 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 6 [0,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 18 ≠ 8 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,3,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 8 [0,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 18 ≠ 9 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,3,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 9 [0,3,7,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 18 ≠ 10 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,3,7,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 10 [0,3,7,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 18 ≠ 11 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,3,7,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 11 [0,3,7,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t6 (t15)

theorem chunk5 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,3,7,12,13,14,15,16,17,18,19,20,21,22,23])
    (d2 : a 2 ∈ [0,11])
    (d3 : a 3 ∈ [0,5,13,15])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    : a 18 ∈ [0,3,7,20] ∧ a 3 ∈ [0,5,13] ∧ a 7 ∈ [0,4,6,7,8,9] := by
  have b0 : a 18 ≠ 12 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 12 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,3,7,13,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 12 [0,3,7,12,13,14,15,16,17,18,19,20,21,22,23] d18 b0
  have b1 : a 18 ≠ 13 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 13 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,3,7,14,15,16,17,18,19,20,21,22,23] := remove (a 18) 13 [0,3,7,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 18 ≠ 14 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 14 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,3,7,15,16,17,18,19,20,21,22,23] := remove (a 18) 14 [0,3,7,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 18 ≠ 15 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 15 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,3,7,16,17,18,19,20,21,22,23] := remove (a 18) 15 [0,3,7,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 18 ≠ 16 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 16 d2 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,3,7,17,18,19,20,21,22,23] := remove (a 18) 16 [0,3,7,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 18 ≠ 17 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 17 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,3,7,18,19,20,21,22,23] := remove (a 18) 17 [0,3,7,17,18,19,20,21,22,23] t4 b5
  have b6 : a 18 ≠ 18 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 18 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,3,7,19,20,21,22,23] := remove (a 18) 18 [0,3,7,18,19,20,21,22,23] t5 b6
  have b7 : a 18 ≠ 19 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 19 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,3,7,20,21,22,23] := remove (a 18) 19 [0,3,7,19,20,21,22,23] t6 b7
  have b8 : a 18 ≠ 21 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 21 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,3,7,20,22,23] := remove (a 18) 21 [0,3,7,20,21,22,23] t7 b8
  have b9 : a 18 ≠ 22 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 22 d2 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,3,7,20,23] := remove (a 18) 22 [0,3,7,20,22,23] t8 b9
  have b10 : a 18 ≠ 23 := exclude [0,11] (fun u v => edge r12 v u) (a 18) (a 2) 23 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,3,7,20] := remove (a 18) 23 [0,3,7,20,23] t9 b10
  have b11 : a 3 ≠ 15 := exclude [0,1,2,3,4,5,6,7,8,9] (edge r13) (a 3) (a 7) 15 d7 c13 (by decide +kernel)
  have t11 : a 3 ∈ [0,5,13] := remove (a 3) 15 [0,5,13,15] d3 b11
  have b12 : a 7 ≠ 1 := exclude [0,5,13] (fun u v => edge r13 v u) (a 7) (a 3) 1 t11 c13 (by decide +kernel)
  have t12 : a 7 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9] d7 b12
  have b13 : a 7 ≠ 2 := exclude [0,5,13] (fun u v => edge r13 v u) (a 7) (a 3) 2 t11 c13 (by decide +kernel)
  have t13 : a 7 ∈ [0,3,4,5,6,7,8,9] := remove (a 7) 2 [0,2,3,4,5,6,7,8,9] t12 b13
  have b14 : a 7 ≠ 3 := exclude [0,5,13] (fun u v => edge r13 v u) (a 7) (a 3) 3 t11 c13 (by decide +kernel)
  have t14 : a 7 ∈ [0,4,5,6,7,8,9] := remove (a 7) 3 [0,3,4,5,6,7,8,9] t13 b14
  have b15 : a 7 ≠ 5 := exclude [0,5,13] (fun u v => edge r13 v u) (a 7) (a 3) 5 t11 c13 (by decide +kernel)
  have t15 : a 7 ∈ [0,4,6,7,8,9] := remove (a 7) 5 [0,4,5,6,7,8,9] t14 b15
  exact And.intro t10 (And.intro t11 (t15))

theorem chunk6 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,4,6,7,8,9])
    (d3 : a 3 ∈ [0,5,13])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 7 ∈ [0,4,6] ∧ a 11 ∈ [0,1,6,9] ∧ a 19 ∈ [0,1,4,5,9,10,11] := by
  have b0 : a 7 ≠ 7 := exclude [0,5,13] (fun u v => edge r13 v u) (a 7) (a 3) 7 d3 c13 (by decide +kernel)
  have t0 : a 7 ∈ [0,4,6,8,9] := remove (a 7) 7 [0,4,6,7,8,9] d7 b0
  have b1 : a 7 ≠ 8 := exclude [0,5,13] (fun u v => edge r13 v u) (a 7) (a 3) 8 d3 c13 (by decide +kernel)
  have t1 : a 7 ∈ [0,4,6,9] := remove (a 7) 8 [0,4,6,8,9] t0 b1
  have b2 : a 7 ≠ 9 := exclude [0,5,13] (fun u v => edge r13 v u) (a 7) (a 3) 9 d3 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0,4,6] := remove (a 7) 9 [0,4,6,9] t1 b2
  have b3 : a 11 ≠ 2 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 11) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b3
  have b4 : a 11 ≠ 3 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 11) 3 [0,1,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 11 ≠ 4 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 11) 4 [0,1,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 11 ≠ 5 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t6 : a 11 ∈ [0,1,6,7,8,9,10,11] := remove (a 11) 5 [0,1,5,6,7,8,9,10,11] t5 b6
  have b7 : a 11 ≠ 7 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 7 d3 c14 (by decide +kernel)
  have t7 : a 11 ∈ [0,1,6,8,9,10,11] := remove (a 11) 7 [0,1,6,7,8,9,10,11] t6 b7
  have b8 : a 11 ≠ 8 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 8 d3 c14 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,6,9,10,11] := remove (a 11) 8 [0,1,6,8,9,10,11] t7 b8
  have b9 : a 11 ≠ 10 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 10 d3 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,6,9,11] := remove (a 11) 10 [0,1,6,9,10,11] t8 b9
  have b10 : a 11 ≠ 11 := exclude [0,5,13] (fun u v => edge r14 v u) (a 11) (a 3) 11 d3 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,1,6,9] := remove (a 11) 11 [0,1,6,9,11] t9 b10
  have b11 : a 19 ≠ 2 := exclude [0,5,13] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t11 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b11
  have b12 : a 19 ≠ 3 := exclude [0,5,13] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 19 ≠ 6 := exclude [0,5,13] (fun u v => edge r15 v u) (a 19) (a 3) 6 d3 c15 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 19) 6 [0,1,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 19 ≠ 7 := exclude [0,5,13] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,4,5,8,9,10,11] := remove (a 19) 7 [0,1,4,5,7,8,9,10,11] t13 b14
  have b15 : a 19 ≠ 8 := exclude [0,5,13] (fun u v => edge r15 v u) (a 19) (a 3) 8 d3 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,4,5,9,10,11] := remove (a 19) 8 [0,1,4,5,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t10 (t15))

theorem chunk7 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,4,5,9,10,11])
    (d3 : a 3 ∈ [0,5,13])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,3,6,9,19,20])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    : a 19 ∈ [0,1,4,5,11] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0,19] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0,4,5,11] := by
  have b0 : a 19 ≠ 9 := exclude [0,5,13] (fun u v => edge r15 v u) (a 19) (a 3) 9 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,4,5,10,11] := remove (a 19) 9 [0,1,4,5,9,10,11] d19 b0
  have b1 : a 19 ≠ 10 := exclude [0,5,13] (fun u v => edge r15 v u) (a 19) (a 3) 10 d3 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,4,5,11] := remove (a 19) 10 [0,1,4,5,10,11] t0 b1
  have b2 : a 4 ≠ 1 := exclude [0,3,6,9,19,20] (edge r17) (a 4) (a 6) 1 d6 c17 (by decide +kernel)
  have t2 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b2
  have b3 : a 6 ≠ 3 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 3 t2 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0,6,9,19,20] := remove (a 6) 3 [0,3,6,9,19,20] d6 b3
  have b4 : a 6 ≠ 6 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 6 t2 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0,9,19,20] := remove (a 6) 6 [0,6,9,19,20] t3 b4
  have b5 : a 6 ≠ 9 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 9 t2 c17 (by decide +kernel)
  have t5 : a 6 ∈ [0,19,20] := remove (a 6) 9 [0,9,19,20] t4 b5
  have b6 : a 6 ≠ 20 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 20 t2 c17 (by decide +kernel)
  have t6 : a 6 ∈ [0,19] := remove (a 6) 20 [0,19,20] t5 b6
  have b7 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t2 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b7
  have b8 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 t2 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 20) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b8
  have b9 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 t2 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 20) 2 [0,2,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 20 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 3 t2 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 t2 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0,4,5,7,8,9,10,11] := remove (a 20) 6 [0,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 20 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 7 t2 c19 (by decide +kernel)
  have t12 : a 20 ∈ [0,4,5,8,9,10,11] := remove (a 20) 7 [0,4,5,7,8,9,10,11] t11 b12
  have b13 : a 20 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 8 t2 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0,4,5,9,10,11] := remove (a 20) 8 [0,4,5,8,9,10,11] t12 b13
  have b14 : a 20 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 9 t2 c19 (by decide +kernel)
  have t14 : a 20 ∈ [0,4,5,10,11] := remove (a 20) 9 [0,4,5,9,10,11] t13 b14
  have b15 : a 20 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 10 t2 c19 (by decide +kernel)
  have t15 : a 20 ∈ [0,4,5,11] := remove (a 20) 10 [0,4,5,10,11] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t6 (And.intro t7 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_186
