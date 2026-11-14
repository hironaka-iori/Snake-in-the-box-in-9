import PartitionData205_214
namespace PartitionCover205_214
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    : a 2 ∈ [0,1,4] ∧ a 4 ∈ [0] ∧ a 8 ∈ [0,1,4,5,9,10,11] := by
  have b0 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,1,3,4,5] := remove (a 2) 2 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,1,4,5] := remove (a 2) 3 [0,1,3,4,5] t0 b1
  have b2 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,1,4] := remove (a 2) 5 [0,1,4,5] t1 b2
  have b3 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2,3,4,5,6,7,8] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8] d4 b3
  have b4 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,3,4,5,6,7,8] := remove (a 4) 2 [0,2,3,4,5,6,7,8] t3 b4
  have b5 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,4,5,6,7,8] := remove (a 4) 3 [0,3,4,5,6,7,8] t4 b5
  have b6 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,5,6,7,8] := remove (a 4) 4 [0,4,5,6,7,8] t5 b6
  have b7 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,6,7,8] := remove (a 4) 5 [0,5,6,7,8] t6 b7
  have b8 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,7,8] := remove (a 4) 6 [0,6,7,8] t7 b8
  have b9 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,8] := remove (a 4) 7 [0,7,8] t8 b9
  have b10 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0] := remove (a 4) 8 [0,8] t9 b10
  have b11 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 8) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d8 b11
  have b12 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t12 : a 8 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 8) 3 [0,1,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 8 ≠ 6 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 6 d0 c3 (by decide +kernel)
  have t13 : a 8 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 8) 6 [0,1,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 8 ≠ 7 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 7 d0 c3 (by decide +kernel)
  have t14 : a 8 ∈ [0,1,4,5,8,9,10,11] := remove (a 8) 7 [0,1,4,5,7,8,9,10,11] t13 b14
  have b15 : a 8 ≠ 8 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 8 d0 c3 (by decide +kernel)
  have t15 : a 8 ∈ [0,1,4,5,9,10,11] := remove (a 8) 8 [0,1,4,5,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t10 (t15))

theorem chunk1 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,4,5,9,10,11])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    : a 8 ∈ [0,1,4,5] ∧ a 16 ∈ [0,1,6,7,17] := by
  have b0 : a 8 ≠ 9 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 9 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,4,5,10,11] := remove (a 8) 9 [0,1,4,5,9,10,11] d8 b0
  have b1 : a 8 ≠ 10 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 10 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,4,5,11] := remove (a 8) 10 [0,1,4,5,10,11] t0 b1
  have b2 : a 8 ≠ 11 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 11 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,4,5] := remove (a 8) 11 [0,1,4,5,11] t1 b2
  have b3 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d16 b3
  have b4 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,6,7,9,10,11,12,13,14,15,16,17] := remove (a 16) 8 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,1,6,7,10,11,12,13,14,15,16,17] := remove (a 16) 9 [0,1,6,7,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 16 ≠ 10 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 10 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,6,7,11,12,13,14,15,16,17] := remove (a 16) 10 [0,1,6,7,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 16 ≠ 11 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 11 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,6,7,12,13,14,15,16,17] := remove (a 16) 11 [0,1,6,7,11,12,13,14,15,16,17] t9 b10
  have b11 : a 16 ≠ 12 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 12 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,6,7,13,14,15,16,17] := remove (a 16) 12 [0,1,6,7,12,13,14,15,16,17] t10 b11
  have b12 : a 16 ≠ 13 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 13 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,6,7,14,15,16,17] := remove (a 16) 13 [0,1,6,7,13,14,15,16,17] t11 b12
  have b13 : a 16 ≠ 14 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 14 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,6,7,15,16,17] := remove (a 16) 14 [0,1,6,7,14,15,16,17] t12 b13
  have b14 : a 16 ≠ 15 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 15 d0 c4 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,6,7,16,17] := remove (a 16) 15 [0,1,6,7,15,16,17] t13 b14
  have b15 : a 16 ≠ 16 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 16 d0 c4 (by decide +kernel)
  have t15 : a 16 ∈ [0,1,6,7,17] := remove (a 16) 16 [0,1,6,7,16,17] t14 b15
  exact And.intro t2 (t15)

theorem chunk2 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,6,7,17])
    (d0 : a 0 ∈ [0])
    (d2 : a 2 ∈ [0,1,4])
    (d3 : a 3 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d18 : a 18 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7])
    (c4 : edge r4 (a 0) (a 16)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    : a 16 ∈ [0,1,6,7] ∧ a 2 ∈ [0,1] ∧ a 3 ∈ [0,2] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0,2] ∧ a 18 ∈ [0,2] ∧ a 7 ∈ [0,1,4,5,6,7] := by
  have b0 : a 16 ≠ 17 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 17 d0 c4 (by decide +kernel)
  have t0 : a 16 ∈ [0,1,6,7] := remove (a 16) 17 [0,1,6,7,17] d16 b0
  have b1 : a 2 ≠ 4 := exclude [0,1,2,3] (edge r9) (a 2) (a 3) 4 d3 c9 (by decide +kernel)
  have t1 : a 2 ∈ [0,1] := remove (a 2) 4 [0,1,4] d2 b1
  have b2 : a 3 ≠ 1 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 1 t1 c9 (by decide +kernel)
  have t2 : a 3 ∈ [0,2,3] := remove (a 3) 1 [0,1,2,3] d3 b2
  have b3 : a 3 ≠ 3 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 3 t1 c9 (by decide +kernel)
  have t3 : a 3 ∈ [0,2] := remove (a 3) 3 [0,2,3] t2 b3
  have b4 : a 6 ≠ 1 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 1 t1 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,2] := remove (a 6) 1 [0,1,2] d6 b4
  have b5 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r10 v u) (a 6) (a 2) 2 t1 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 2 [0,2] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 1 t1 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3,4,5] := remove (a 10) 1 [0,1,2,3,4,5] d10 b6
  have b7 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 3 t1 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,2,4,5] := remove (a 10) 3 [0,2,3,4,5] t6 b7
  have b8 : a 10 ≠ 4 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 4 t1 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,2,5] := remove (a 10) 4 [0,2,4,5] t7 b8
  have b9 : a 10 ≠ 5 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 5 t1 c11 (by decide +kernel)
  have t9 : a 10 ∈ [0,2] := remove (a 10) 5 [0,2,5] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 1 t1 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,3,4,5] := remove (a 18) 1 [0,1,2,3,4,5] d18 b10
  have b11 : a 18 ≠ 3 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 3 t1 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,2,4,5] := remove (a 18) 3 [0,2,3,4,5] t10 b11
  have b12 : a 18 ≠ 4 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 4 t1 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,5] := remove (a 18) 4 [0,2,4,5] t11 b12
  have b13 : a 18 ≠ 5 := exclude [0,1] (fun u v => edge r12 v u) (a 18) (a 2) 5 t1 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,2] := remove (a 18) 5 [0,2,5] t12 b13
  have b14 : a 7 ≠ 2 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 2 t3 c13 (by decide +kernel)
  have t14 : a 7 ∈ [0,1,3,4,5,6,7] := remove (a 7) 2 [0,1,2,3,4,5,6,7] d7 b14
  have b15 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 3 t3 c13 (by decide +kernel)
  have t15 : a 7 ∈ [0,1,4,5,6,7] := remove (a 7) 3 [0,1,3,4,5,6,7] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t5 (And.intro t9 (And.intro t13 (t15))))))

theorem chunk3 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,4,5,6,7])
    (d3 : a 3 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 7 ∈ [0,1,4,5] ∧ a 11 ∈ [0,2] ∧ a 19 ∈ [0,1] ∧ a 5 ∈ [0,1] ∧ a 12 ∈ [0,3,4,5] := by
  have b0 : a 7 ≠ 6 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 6 d3 c13 (by decide +kernel)
  have t0 : a 7 ∈ [0,1,4,5,7] := remove (a 7) 6 [0,1,4,5,6,7] d7 b0
  have b1 : a 7 ≠ 7 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 7 d3 c13 (by decide +kernel)
  have t1 : a 7 ∈ [0,1,4,5] := remove (a 7) 7 [0,1,4,5,7] t0 b1
  have b2 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b2
  have b3 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 3 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,2,4,5] := remove (a 11) 3 [0,2,3,4,5] t2 b3
  have b4 : a 11 ≠ 4 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,2,5] := remove (a 11) 4 [0,2,4,5] t3 b4
  have b5 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0,2] := remove (a 11) 5 [0,2,5] t4 b5
  have b6 : a 19 ≠ 2 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0,1,3,4,5] := remove (a 19) 2 [0,1,2,3,4,5] d19 b6
  have b7 : a 19 ≠ 3 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,4,5] := remove (a 19) 3 [0,1,3,4,5] t6 b7
  have b8 : a 19 ≠ 4 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 4 d3 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,5] := remove (a 19) 4 [0,1,4,5] t7 b8
  have b9 : a 19 ≠ 5 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 5 d3 c15 (by decide +kernel)
  have t9 : a 19 ∈ [0,1] := remove (a 19) 5 [0,1,5] t8 b9
  have b10 : a 5 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 2 d4 c16 (by decide +kernel)
  have t10 : a 5 ∈ [0,1,3,4,5] := remove (a 5) 2 [0,1,2,3,4,5] d5 b10
  have b11 : a 5 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,4,5] := remove (a 5) 3 [0,1,3,4,5] t10 b11
  have b12 : a 5 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,5] := remove (a 5) 4 [0,1,4,5] t11 b12
  have b13 : a 5 ≠ 5 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 5 d4 c16 (by decide +kernel)
  have t13 : a 5 ∈ [0,1] := remove (a 5) 5 [0,1,5] t12 b13
  have b14 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,3,4,5] := remove (a 12) 1 [0,1,2,3,4,5] d12 b14
  have b15 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,3,4,5] := remove (a 12) 2 [0,2,3,4,5] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t9 (And.intro t13 (t15))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_214
