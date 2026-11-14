import PartitionData205_161
namespace PartitionCover205_161
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,12,13,14,15,16,17,18,19])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6])
    (d4 : a 4 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 11 ∈ [0] ∧ a 5 ∈ [0] ∧ a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := by
  have b0 : a 11 ≠ 12 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 12 d3 c11 (by decide +kernel)
  have t0 : a 11 ∈ [0,13,14,15,16,17,18,19] := remove (a 11) 12 [0,12,13,14,15,16,17,18,19] d11 b0
  have b1 : a 11 ≠ 13 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 13 d3 c11 (by decide +kernel)
  have t1 : a 11 ∈ [0,14,15,16,17,18,19] := remove (a 11) 13 [0,13,14,15,16,17,18,19] t0 b1
  have b2 : a 11 ≠ 14 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 14 d3 c11 (by decide +kernel)
  have t2 : a 11 ∈ [0,15,16,17,18,19] := remove (a 11) 14 [0,14,15,16,17,18,19] t1 b2
  have b3 : a 11 ≠ 15 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 15 d3 c11 (by decide +kernel)
  have t3 : a 11 ∈ [0,16,17,18,19] := remove (a 11) 15 [0,15,16,17,18,19] t2 b3
  have b4 : a 11 ≠ 16 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 16 d3 c11 (by decide +kernel)
  have t4 : a 11 ∈ [0,17,18,19] := remove (a 11) 16 [0,16,17,18,19] t3 b4
  have b5 : a 11 ≠ 17 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 17 d3 c11 (by decide +kernel)
  have t5 : a 11 ∈ [0,18,19] := remove (a 11) 17 [0,17,18,19] t4 b5
  have b6 : a 11 ≠ 18 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 18 d3 c11 (by decide +kernel)
  have t6 : a 11 ∈ [0,19] := remove (a 11) 18 [0,18,19] t5 b6
  have b7 : a 11 ≠ 19 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 19 d3 c11 (by decide +kernel)
  have t7 : a 11 ∈ [0] := remove (a 11) 19 [0,19] t6 b7
  have b8 : a 5 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 1 d4 c12 (by decide +kernel)
  have t8 : a 5 ∈ [0,2,3,4,5,6] := remove (a 5) 1 [0,1,2,3,4,5,6] d5 b8
  have b9 : a 5 ≠ 2 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 2 d4 c12 (by decide +kernel)
  have t9 : a 5 ∈ [0,3,4,5,6] := remove (a 5) 2 [0,2,3,4,5,6] t8 b9
  have b10 : a 5 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 3 d4 c12 (by decide +kernel)
  have t10 : a 5 ∈ [0,4,5,6] := remove (a 5) 3 [0,3,4,5,6] t9 b10
  have b11 : a 5 ≠ 4 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 4 d4 c12 (by decide +kernel)
  have t11 : a 5 ∈ [0,5,6] := remove (a 5) 4 [0,4,5,6] t10 b11
  have b12 : a 5 ≠ 5 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 5 d4 c12 (by decide +kernel)
  have t12 : a 5 ∈ [0,6] := remove (a 5) 5 [0,5,6] t11 b12
  have b13 : a 5 ≠ 6 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 6 d4 c12 (by decide +kernel)
  have t13 : a 5 ∈ [0] := remove (a 5) 6 [0,6] t12 b13
  have b14 : a 12 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 1 d4 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] d12 b14
  have b15 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 d4 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t14 b15
  exact And.intro t7 (And.intro t13 (t15))

theorem chunk9 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (d4 : a 4 ∈ [0])
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 12 ∈ [0,19,20,21,22,23,24,25,26,27] := by
  have b0 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] d12 b0
  have b1 : a 12 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 4 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t0 b1
  have b2 : a 12 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 5 d4 c14 (by decide +kernel)
  have t2 : a 12 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t1 b2
  have b3 : a 12 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 6 d4 c14 (by decide +kernel)
  have t3 : a 12 ∈ [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t2 b3
  have b4 : a 12 ≠ 7 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 7 d4 c14 (by decide +kernel)
  have t4 : a 12 ∈ [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 7 [0,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t3 b4
  have b5 : a 12 ≠ 8 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 8 d4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 8 [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t4 b5
  have b6 : a 12 ≠ 9 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 9 d4 c14 (by decide +kernel)
  have t6 : a 12 ∈ [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 9 [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t5 b6
  have b7 : a 12 ≠ 10 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 10 d4 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 10 [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t6 b7
  have b8 : a 12 ≠ 11 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 11 d4 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 11 [0,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t7 b8
  have b9 : a 12 ≠ 12 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 12 d4 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 12 [0,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t8 b9
  have b10 : a 12 ≠ 13 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 13 d4 c14 (by decide +kernel)
  have t10 : a 12 ∈ [0,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 13 [0,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t9 b10
  have b11 : a 12 ≠ 14 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 14 d4 c14 (by decide +kernel)
  have t11 : a 12 ∈ [0,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 14 [0,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t10 b11
  have b12 : a 12 ≠ 15 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 15 d4 c14 (by decide +kernel)
  have t12 : a 12 ∈ [0,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 15 [0,15,16,17,18,19,20,21,22,23,24,25,26,27] t11 b12
  have b13 : a 12 ≠ 16 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 16 d4 c14 (by decide +kernel)
  have t13 : a 12 ∈ [0,17,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 16 [0,16,17,18,19,20,21,22,23,24,25,26,27] t12 b13
  have b14 : a 12 ≠ 17 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 17 d4 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,18,19,20,21,22,23,24,25,26,27] := remove (a 12) 17 [0,17,18,19,20,21,22,23,24,25,26,27] t13 b14
  have b15 : a 12 ≠ 18 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 18 d4 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,19,20,21,22,23,24,25,26,27] := remove (a 12) 18 [0,18,19,20,21,22,23,24,25,26,27] t14 b15
  exact t15

theorem chunk10 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,19,20,21,22,23,24,25,26,27])
    (d4 : a 4 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (d5 : a 5 ∈ [0])
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    : a 12 ∈ [0] ∧ a 13 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := by
  have b0 : a 12 ≠ 19 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 19 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,20,21,22,23,24,25,26,27] := remove (a 12) 19 [0,19,20,21,22,23,24,25,26,27] d12 b0
  have b1 : a 12 ≠ 20 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 20 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,21,22,23,24,25,26,27] := remove (a 12) 20 [0,20,21,22,23,24,25,26,27] t0 b1
  have b2 : a 12 ≠ 21 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 21 d4 c14 (by decide +kernel)
  have t2 : a 12 ∈ [0,22,23,24,25,26,27] := remove (a 12) 21 [0,21,22,23,24,25,26,27] t1 b2
  have b3 : a 12 ≠ 22 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 22 d4 c14 (by decide +kernel)
  have t3 : a 12 ∈ [0,23,24,25,26,27] := remove (a 12) 22 [0,22,23,24,25,26,27] t2 b3
  have b4 : a 12 ≠ 23 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 23 d4 c14 (by decide +kernel)
  have t4 : a 12 ∈ [0,24,25,26,27] := remove (a 12) 23 [0,23,24,25,26,27] t3 b4
  have b5 : a 12 ≠ 24 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 24 d4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [0,25,26,27] := remove (a 12) 24 [0,24,25,26,27] t4 b5
  have b6 : a 12 ≠ 25 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 25 d4 c14 (by decide +kernel)
  have t6 : a 12 ∈ [0,26,27] := remove (a 12) 25 [0,25,26,27] t5 b6
  have b7 : a 12 ≠ 26 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 26 d4 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0,27] := remove (a 12) 26 [0,26,27] t6 b7
  have b8 : a 12 ≠ 27 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 27 d4 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0] := remove (a 12) 27 [0,27] t7 b8
  have b9 : a 13 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] d13 b9
  have b10 : a 13 ≠ 5 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t9 b10
  have b11 : a 13 ≠ 6 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t10 b11
  have b12 : a 13 ≠ 7 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t11 b12
  have b13 : a 13 ≠ 8 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 8 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t12 b13
  have b14 : a 13 ≠ 9 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 9 d5 c16 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t13 b14
  have b15 : a 13 ≠ 10 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 10 d5 c16 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t14 b15
  exact And.intro t8 (t15)

theorem chunk11 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27])
    (d5 : a 5 ∈ [0])
    (c16 : edge r16 (a 5) (a 13)=true)
    : a 13 ∈ [0,1,2,3,27] := by
  have b0 : a 13 ≠ 11 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 11 d5 c16 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] d13 b0
  have b1 : a 13 ≠ 12 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 12 d5 c16 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,2,3,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 12 [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t0 b1
  have b2 : a 13 ≠ 13 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 13 d5 c16 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,2,3,14,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 13 [0,1,2,3,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t1 b2
  have b3 : a 13 ≠ 14 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 14 d5 c16 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,2,3,15,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 14 [0,1,2,3,14,15,16,17,18,19,20,21,22,23,24,25,26,27] t2 b3
  have b4 : a 13 ≠ 15 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 15 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,2,3,16,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 15 [0,1,2,3,15,16,17,18,19,20,21,22,23,24,25,26,27] t3 b4
  have b5 : a 13 ≠ 16 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 16 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,2,3,17,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 16 [0,1,2,3,16,17,18,19,20,21,22,23,24,25,26,27] t4 b5
  have b6 : a 13 ≠ 17 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 17 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,2,3,18,19,20,21,22,23,24,25,26,27] := remove (a 13) 17 [0,1,2,3,17,18,19,20,21,22,23,24,25,26,27] t5 b6
  have b7 : a 13 ≠ 18 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 18 d5 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,2,3,19,20,21,22,23,24,25,26,27] := remove (a 13) 18 [0,1,2,3,18,19,20,21,22,23,24,25,26,27] t6 b7
  have b8 : a 13 ≠ 19 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 19 d5 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,2,3,20,21,22,23,24,25,26,27] := remove (a 13) 19 [0,1,2,3,19,20,21,22,23,24,25,26,27] t7 b8
  have b9 : a 13 ≠ 20 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 20 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,2,3,21,22,23,24,25,26,27] := remove (a 13) 20 [0,1,2,3,20,21,22,23,24,25,26,27] t8 b9
  have b10 : a 13 ≠ 21 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 21 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,2,3,22,23,24,25,26,27] := remove (a 13) 21 [0,1,2,3,21,22,23,24,25,26,27] t9 b10
  have b11 : a 13 ≠ 22 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 22 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,2,3,23,24,25,26,27] := remove (a 13) 22 [0,1,2,3,22,23,24,25,26,27] t10 b11
  have b12 : a 13 ≠ 23 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 23 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,2,3,24,25,26,27] := remove (a 13) 23 [0,1,2,3,23,24,25,26,27] t11 b12
  have b13 : a 13 ≠ 24 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 24 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,2,3,25,26,27] := remove (a 13) 24 [0,1,2,3,24,25,26,27] t12 b13
  have b14 : a 13 ≠ 25 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 25 d5 c16 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,2,3,26,27] := remove (a 13) 25 [0,1,2,3,25,26,27] t13 b14
  have b15 : a 13 ≠ 26 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 26 d5 c16 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,2,3,27] := remove (a 13) 26 [0,1,2,3,26,27] t14 b15
  exact t15

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_161
