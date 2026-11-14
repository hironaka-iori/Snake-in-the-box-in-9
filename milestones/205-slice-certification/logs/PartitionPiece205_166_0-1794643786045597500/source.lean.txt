import PartitionData205_166
namespace PartitionCover205_166
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 2 ∈ [0] ∧ a 6 ∈ [0,2] ∧ a 10 ∈ [0,2] ∧ a 18 ∈ [0,6,9] := by
  have b0 : a 2 ≠ 1 := exclude [0,1,2,3,4,5] (edge r10) (a 2) (a 6) 1 d6 c10 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 t0 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,3,4,5] := remove (a 6) 1 [0,1,2,3,4,5] d6 b1
  have b2 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 t0 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0,2,4,5] := remove (a 6) 3 [0,2,3,4,5] t1 b2
  have b3 : a 6 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 4 t0 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0,2,5] := remove (a 6) 4 [0,2,4,5] t2 b3
  have b4 : a 6 ≠ 5 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 5 t0 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0,2] := remove (a 6) 5 [0,2,5] t3 b4
  have b5 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 t0 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0,2,3,4,5] := remove (a 10) 1 [0,1,2,3,4,5] d10 b5
  have b6 : a 10 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 3 t0 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,4,5] := remove (a 10) 3 [0,2,3,4,5] t5 b6
  have b7 : a 10 ≠ 4 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 4 t0 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,2,5] := remove (a 10) 4 [0,2,4,5] t6 b7
  have b8 : a 10 ≠ 5 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 5 t0 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,2] := remove (a 10) 5 [0,2,5] t7 b8
  have b9 : a 18 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 1 t0 c12 (by decide +kernel)
  have t9 : a 18 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9] d18 b9
  have b10 : a 18 ≠ 2 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 2 t0 c12 (by decide +kernel)
  have t10 : a 18 ∈ [0,3,4,5,6,7,8,9] := remove (a 18) 2 [0,2,3,4,5,6,7,8,9] t9 b10
  have b11 : a 18 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 3 t0 c12 (by decide +kernel)
  have t11 : a 18 ∈ [0,4,5,6,7,8,9] := remove (a 18) 3 [0,3,4,5,6,7,8,9] t10 b11
  have b12 : a 18 ≠ 4 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 4 t0 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,5,6,7,8,9] := remove (a 18) 4 [0,4,5,6,7,8,9] t11 b12
  have b13 : a 18 ≠ 5 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 5 t0 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,6,7,8,9] := remove (a 18) 5 [0,5,6,7,8,9] t12 b13
  have b14 : a 18 ≠ 7 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 7 t0 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,6,8,9] := remove (a 18) 7 [0,6,7,8,9] t13 b14
  have b15 : a 18 ≠ 8 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 8 t0 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,6,9] := remove (a 18) 8 [0,6,8,9] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t8 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,6,9])
    (d2 : a 2 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,2])
    (d12 : a 12 ∈ [0,1,2])
    (d7 : a 7 ∈ [0,1,2])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 18 ∈ [0,6] ∧ a 4 ∈ [0,2] ∧ a 12 ∈ [0,1] ∧ a 7 ∈ [0,1] ∧ a 14 ∈ [0,2] ∧ a 22 ∈ [0,3,7,8] := by
  have b0 : a 18 ≠ 9 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,6] := remove (a 18) 9 [0,6,9] d18 b0
  have b1 : a 4 ≠ 1 := exclude [0,2] (edge r17) (a 4) (a 6) 1 d6 c17 (by decide +kernel)
  have t1 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b1
  have b2 : a 4 ≠ 3 := exclude [0,2] (edge r17) (a 4) (a 6) 3 d6 c17 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,4,5] := remove (a 4) 3 [0,2,3,4,5] t1 b2
  have b3 : a 4 ≠ 4 := exclude [0,2] (edge r17) (a 4) (a 6) 4 d6 c17 (by decide +kernel)
  have t3 : a 4 ∈ [0,2,5] := remove (a 4) 4 [0,2,4,5] t2 b3
  have b4 : a 4 ≠ 5 := exclude [0,2] (edge r17) (a 4) (a 6) 5 d6 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0,2] := remove (a 4) 5 [0,2,5] t3 b4
  have b5 : a 12 ≠ 2 := exclude [0,2] (fun u v => edge r18 v u) (a 12) (a 4) 2 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0,1] := remove (a 12) 2 [0,1,2] d12 b5
  have b6 : a 7 ≠ 2 := exclude [0,2] (fun u v => edge r23 v u) (a 7) (a 6) 2 d6 c23 (by decide +kernel)
  have t6 : a 7 ∈ [0,1] := remove (a 7) 2 [0,1,2] d7 b6
  have b7 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b7
  have b8 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,4,5] := remove (a 14) 3 [0,2,3,4,5] t7 b8
  have b9 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 4 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,2,5] := remove (a 14) 4 [0,2,4,5] t8 b9
  have b10 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,2] := remove (a 14) 5 [0,2,5] t9 b10
  have b11 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,3,4,5,6,7,8] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8] d22 b11
  have b12 : a 22 ≠ 2 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,3,4,5,6,7,8] := remove (a 22) 2 [0,2,3,4,5,6,7,8] t11 b12
  have b13 : a 22 ≠ 4 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,3,5,6,7,8] := remove (a 22) 4 [0,3,4,5,6,7,8] t12 b13
  have b14 : a 22 ≠ 5 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,3,6,7,8] := remove (a 22) 5 [0,3,5,6,7,8] t13 b14
  have b15 : a 22 ≠ 6 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0,3,7,8] := remove (a 22) 6 [0,3,6,7,8] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t10 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,3,7,8])
    (d6 : a 6 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2])
    (d7 : a 7 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 22 ∈ [0,3] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0,1,6,7] ∧ a 8 ∈ [0,1] ∧ a 24 ∈ [0,2,3,5] ∧ a 11 ∈ [0] := by
  have b0 : a 22 ≠ 7 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,3,8] := remove (a 22) 7 [0,3,7,8] d22 b0
  have b1 : a 22 ≠ 8 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,3] := remove (a 22) 8 [0,3,8] t0 b1
  have b2 : a 15 ≠ 1 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 1 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,2] := remove (a 15) 1 [0,1,2] d15 b2
  have b3 : a 15 ≠ 2 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0] := remove (a 15) 2 [0,2] t2 b3
  have b4 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 23) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b4
  have b5 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 23 ≠ 4 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 23) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 23 ≠ 5 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,6,7,8,9,10,11] := remove (a 23) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 23 ≠ 8 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,6,7,9,10,11] := remove (a 23) 8 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 23 ≠ 9 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 9 d7 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,6,7,10,11] := remove (a 23) 9 [0,1,6,7,9,10,11] t8 b9
  have b10 : a 23 ≠ 10 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 10 d7 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,6,7,11] := remove (a 23) 10 [0,1,6,7,10,11] t9 b10
  have b11 : a 23 ≠ 11 := exclude [0,1] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,6,7] := remove (a 23) 11 [0,1,6,7,11] t10 b11
  have b12 : a 8 ≠ 2 := exclude [0,2] (edge r29) (a 8) (a 10) 2 d10 c29 (by decide +kernel)
  have t12 : a 8 ∈ [0,1] := remove (a 8) 2 [0,1,2] d8 b12
  have b13 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 t12 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,3,4,5] := remove (a 24) 1 [0,1,2,3,4,5] d24 b13
  have b14 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 t12 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,3,5] := remove (a 24) 4 [0,2,3,4,5] t13 b14
  have b15 : a 11 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 1 d9 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b15
  exact And.intro t1 (And.intro t3 (And.intro t11 (And.intro t12 (And.intro t14 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    : a 13 ∈ [0,2,4,6,9,10,11] ∧ a 25 ∈ [0,1,2,3,6,7,8,9] ∧ a 26 ∈ [0,1,4] ∧ a 27 ∈ [0] := by
  have b0 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t0 : a 13 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d13 b0
  have b1 : a 13 ≠ 3 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 13) 3 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 13 ≠ 5 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t2 : a 13 ∈ [0,2,4,6,7,8,9,10,11] := remove (a 13) 5 [0,2,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 13 ≠ 7 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 7 d9 c33 (by decide +kernel)
  have t3 : a 13 ∈ [0,2,4,6,8,9,10,11] := remove (a 13) 7 [0,2,4,6,7,8,9,10,11] t2 b3
  have b4 : a 25 ≠ 4 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 25) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b4
  have b5 : a 25 ≠ 5 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 25) 5 [0,1,2,3,5,6,7,8,9,10,11] t4 b5
  have b6 : a 25 ≠ 10 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,2,3,6,7,8,9,11] := remove (a 25) 10 [0,1,2,3,6,7,8,9,10,11] t5 b6
  have b7 : a 25 ≠ 11 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,2,3,6,7,8,9] := remove (a 25) 11 [0,1,2,3,6,7,8,9,11] t6 b7
  have b8 : a 26 ≠ 2 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,3,4,5,6,7,8] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8] d26 b8
  have b9 : a 26 ≠ 3 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,4,5,6,7,8] := remove (a 26) 3 [0,1,3,4,5,6,7,8] t8 b9
  have b10 : a 26 ≠ 5 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,4,6,7,8] := remove (a 26) 5 [0,1,4,5,6,7,8] t9 b10
  have b11 : a 26 ≠ 6 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,4,7,8] := remove (a 26) 6 [0,1,4,6,7,8] t10 b11
  have b12 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,4,8] := remove (a 26) 7 [0,1,4,7,8] t11 b12
  have b13 : a 26 ≠ 8 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,4] := remove (a 26) 8 [0,1,4,8] t12 b13
  have b14 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b14
  have b15 : a 13 ≠ 8 := exclude [0,1] (fun u v => edge r40 v u) (a 13) (a 12) 8 d12 c40 (by decide +kernel)
  have t15 : a 13 ∈ [0,2,4,6,9,10,11] := remove (a 13) 8 [0,2,4,6,8,9,10,11] t3 b15
  exact And.intro t15 (And.intro t7 (And.intro t13 (t14)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_166
