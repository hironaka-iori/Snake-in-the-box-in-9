import PartitionData205_217
namespace PartitionCover205_217
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,2,12,14,18,20,23])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 6 ∈ [0,2,12,14,18,20] ∧ a 10 ∈ [0,1,2] ∧ a 18 ∈ [0,2,7,9,10,11] := by
  have b0 : a 6 ≠ 23 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 23 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,2,12,14,18,20] := remove (a 6) 23 [0,2,12,14,18,20,23] d6 b0
  have b1 : a 10 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,2,4,5,6,7,8,9,10,11] := remove (a 10) 3 [0,1,2,3,4,5,6,7,8,9,10,11] d10 b1
  have b2 : a 10 ≠ 4 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 4 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,1,2,5,6,7,8,9,10,11] := remove (a 10) 4 [0,1,2,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 10 ≠ 5 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 5 d2 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,1,2,6,7,8,9,10,11] := remove (a 10) 5 [0,1,2,5,6,7,8,9,10,11] t2 b3
  have b4 : a 10 ≠ 6 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,2,7,8,9,10,11] := remove (a 10) 6 [0,1,2,6,7,8,9,10,11] t3 b4
  have b5 : a 10 ≠ 7 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 7 d2 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,2,8,9,10,11] := remove (a 10) 7 [0,1,2,7,8,9,10,11] t4 b5
  have b6 : a 10 ≠ 8 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 8 d2 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,1,2,9,10,11] := remove (a 10) 8 [0,1,2,8,9,10,11] t5 b6
  have b7 : a 10 ≠ 9 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 9 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,1,2,10,11] := remove (a 10) 9 [0,1,2,9,10,11] t6 b7
  have b8 : a 10 ≠ 10 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 10 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,2,11] := remove (a 10) 10 [0,1,2,10,11] t7 b8
  have b9 : a 10 ≠ 11 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 11 d2 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,2] := remove (a 10) 11 [0,1,2,11] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b10
  have b11 : a 18 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 18) 3 [0,2,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 18 ≠ 4 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 4 d2 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 18) 4 [0,2,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 18 ≠ 5 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 5 d2 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,6,7,8,9,10,11] := remove (a 18) 5 [0,2,5,6,7,8,9,10,11] t12 b13
  have b14 : a 18 ≠ 6 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,2,7,8,9,10,11] := remove (a 18) 6 [0,2,6,7,8,9,10,11] t13 b14
  have b15 : a 18 ≠ 8 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,2,7,9,10,11] := remove (a 18) 8 [0,2,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t9 (t15))

theorem chunk9 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2,7,9,10,11])
    (d2 : a 2 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    : a 18 ∈ [0,2,7] ∧ a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] ∧ a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 18 ≠ 9 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,2,7,10,11] := remove (a 18) 9 [0,2,7,9,10,11] d18 b0
  have b1 : a 18 ≠ 10 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,2,7,11] := remove (a 18) 10 [0,2,7,10,11] t0 b1
  have b2 : a 18 ≠ 11 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 11 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,2,7] := remove (a 18) 11 [0,2,7,11] t1 b2
  have b3 : a 7 ≠ 12 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 12 d3 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23] := remove (a 7) 12 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d7 b3
  have b4 : a 7 ≠ 13 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 13 d3 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17,18,19,20,21,22,23] := remove (a 7) 13 [0,1,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 7 ≠ 14 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 14 d3 c13 (by decide +kernel)
  have t5 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17,18,19,20,21,22,23] := remove (a 7) 14 [0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 7 ≠ 15 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 15 d3 c13 (by decide +kernel)
  have t6 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,16,17,18,19,20,21,22,23] := remove (a 7) 15 [0,1,2,3,4,5,6,7,8,9,10,11,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 7 ≠ 16 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 16 d3 c13 (by decide +kernel)
  have t7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,17,18,19,20,21,22,23] := remove (a 7) 16 [0,1,2,3,4,5,6,7,8,9,10,11,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 7 ≠ 17 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 17 d3 c13 (by decide +kernel)
  have t8 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23] := remove (a 7) 17 [0,1,2,3,4,5,6,7,8,9,10,11,17,18,19,20,21,22,23] t7 b8
  have b9 : a 7 ≠ 18 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 18 d3 c13 (by decide +kernel)
  have t9 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,19,20,21,22,23] := remove (a 7) 18 [0,1,2,3,4,5,6,7,8,9,10,11,18,19,20,21,22,23] t8 b9
  have b10 : a 7 ≠ 19 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 19 d3 c13 (by decide +kernel)
  have t10 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,20,21,22,23] := remove (a 7) 19 [0,1,2,3,4,5,6,7,8,9,10,11,19,20,21,22,23] t9 b10
  have b11 : a 7 ≠ 20 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 20 d3 c13 (by decide +kernel)
  have t11 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,21,22,23] := remove (a 7) 20 [0,1,2,3,4,5,6,7,8,9,10,11,20,21,22,23] t10 b11
  have b12 : a 7 ≠ 21 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 21 d3 c13 (by decide +kernel)
  have t12 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,22,23] := remove (a 7) 21 [0,1,2,3,4,5,6,7,8,9,10,11,21,22,23] t11 b12
  have b13 : a 7 ≠ 22 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 22 d3 c13 (by decide +kernel)
  have t13 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,23] := remove (a 7) 22 [0,1,2,3,4,5,6,7,8,9,10,11,22,23] t12 b13
  have b14 : a 7 ≠ 23 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 23 d3 c13 (by decide +kernel)
  have t14 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11] := remove (a 7) 23 [0,1,2,3,4,5,6,7,8,9,10,11,23] t13 b14
  have b15 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 11) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d11 b15
  exact And.intro t2 (And.intro t14 (t15))

theorem chunk10 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d3 : a 3 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,2,12,14,18,20])
    (d4 : a 4 ∈ [0,1,6])
    (d6 : a 6 ∈ [0,2,12,14,18,20])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 11 ∈ [0,4,7,8,9,10,11] ∧ a 19 ∈ [0,1,2,3,4,6,8,9,11] ∧ a 5 ∈ [0,2,12,14] ∧ a 4 ∈ [0,6] ∧ a 6 ∈ [0,2] ∧ a 12 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 11) 2 [0,2,3,4,5,6,7,8,9,10,11] d11 b0
  have b1 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 11) 3 [0,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,4,6,7,8,9,10,11] := remove (a 11) 5 [0,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 11 ≠ 6 := exclude [0,1] (fun u v => edge r14 v u) (a 11) (a 3) 6 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,4,7,8,9,10,11] := remove (a 11) 6 [0,4,6,7,8,9,10,11] t2 b3
  have b4 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,2,3,4,6,7,8,9,10,11] := remove (a 19) 5 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b4
  have b5 : a 19 ≠ 7 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 7 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,1,2,3,4,6,8,9,10,11] := remove (a 19) 7 [0,1,2,3,4,6,7,8,9,10,11] t4 b5
  have b6 : a 19 ≠ 10 := exclude [0,1] (fun u v => edge r15 v u) (a 19) (a 3) 10 d3 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0,1,2,3,4,6,8,9,11] := remove (a 19) 10 [0,1,2,3,4,6,8,9,10,11] t5 b6
  have b7 : a 5 ≠ 18 := exclude [0,1,6] (fun u v => edge r16 v u) (a 5) (a 4) 18 d4 c16 (by decide +kernel)
  have t7 : a 5 ∈ [0,2,12,14,20] := remove (a 5) 18 [0,2,12,14,18,20] d5 b7
  have b8 : a 5 ≠ 20 := exclude [0,1,6] (fun u v => edge r16 v u) (a 5) (a 4) 20 d4 c16 (by decide +kernel)
  have t8 : a 5 ∈ [0,2,12,14] := remove (a 5) 20 [0,2,12,14,20] t7 b8
  have b9 : a 4 ≠ 1 := exclude [0,2,12,14,18,20] (edge r17) (a 4) (a 6) 1 d6 c17 (by decide +kernel)
  have t9 : a 4 ∈ [0,6] := remove (a 4) 1 [0,1,6] d4 b9
  have b10 : a 6 ≠ 12 := exclude [0,6] (fun u v => edge r17 v u) (a 6) (a 4) 12 t9 c17 (by decide +kernel)
  have t10 : a 6 ∈ [0,2,14,18,20] := remove (a 6) 12 [0,2,12,14,18,20] d6 b10
  have b11 : a 6 ≠ 14 := exclude [0,6] (fun u v => edge r17 v u) (a 6) (a 4) 14 t9 c17 (by decide +kernel)
  have t11 : a 6 ∈ [0,2,18,20] := remove (a 6) 14 [0,2,14,18,20] t10 b11
  have b12 : a 6 ≠ 18 := exclude [0,6] (fun u v => edge r17 v u) (a 6) (a 4) 18 t9 c17 (by decide +kernel)
  have t12 : a 6 ∈ [0,2,20] := remove (a 6) 18 [0,2,18,20] t11 b12
  have b13 : a 6 ≠ 20 := exclude [0,6] (fun u v => edge r17 v u) (a 6) (a 4) 20 t9 c17 (by decide +kernel)
  have t13 : a 6 ∈ [0,2] := remove (a 6) 20 [0,2,20] t12 b13
  have b14 : a 12 ≠ 6 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 6 t9 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b14
  have b15 : a 12 ≠ 7 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 7 t9 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk11 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d4 : a 4 ∈ [0,6])
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 12 ∈ [0,1,2,3,4,5] := by
  have b0 : a 12 ≠ 8 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d12 b0
  have b1 : a 12 ≠ 9 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 12 ≠ 10 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 10 d4 c18 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 12 ≠ 11 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 11 d4 c18 (by decide +kernel)
  have t3 : a 12 ∈ [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 12 ≠ 12 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 12 d4 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 12 [0,1,2,3,4,5,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 12 ≠ 13 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 13 d4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] := remove (a 12) 13 [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 12 ≠ 14 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 14 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] := remove (a 12) 14 [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 12 ≠ 15 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 15 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,2,3,4,5,16,17,18,19,20,21,22,23] := remove (a 12) 15 [0,1,2,3,4,5,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 12 ≠ 16 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 16 d4 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,2,3,4,5,17,18,19,20,21,22,23] := remove (a 12) 16 [0,1,2,3,4,5,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 12 ≠ 17 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 17 d4 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,2,3,4,5,18,19,20,21,22,23] := remove (a 12) 17 [0,1,2,3,4,5,17,18,19,20,21,22,23] t8 b9
  have b10 : a 12 ≠ 18 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 18 d4 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,2,3,4,5,19,20,21,22,23] := remove (a 12) 18 [0,1,2,3,4,5,18,19,20,21,22,23] t9 b10
  have b11 : a 12 ≠ 19 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 19 d4 c18 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,2,3,4,5,20,21,22,23] := remove (a 12) 19 [0,1,2,3,4,5,19,20,21,22,23] t10 b11
  have b12 : a 12 ≠ 20 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 20 d4 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,2,3,4,5,21,22,23] := remove (a 12) 20 [0,1,2,3,4,5,20,21,22,23] t11 b12
  have b13 : a 12 ≠ 21 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 21 d4 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,2,3,4,5,22,23] := remove (a 12) 21 [0,1,2,3,4,5,21,22,23] t12 b13
  have b14 : a 12 ≠ 22 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 22 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,2,3,4,5,23] := remove (a 12) 22 [0,1,2,3,4,5,22,23] t13 b14
  have b15 : a 12 ≠ 23 := exclude [0,6] (fun u v => edge r18 v u) (a 12) (a 4) 23 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,2,3,4,5] := remove (a 12) 23 [0,1,2,3,4,5,23] t14 b15
  exact t15

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_217
