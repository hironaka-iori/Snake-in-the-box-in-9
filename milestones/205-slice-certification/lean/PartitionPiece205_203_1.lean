import PartitionData205_203
namespace PartitionCover205_203
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,2,6,8,9,10,11])
    (d4 : a 4 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0,4])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 12 ∈ [0,2,6,8,10,11] ∧ a 7 ∈ [0,2] ∧ a 14 ∈ [0,1,2,3,4,5,6,8,10,11] ∧ a 22 ∈ [0,1,6] ∧ a 15 ∈ [0,1,4,5,6,7,8] := by
  have b0 : a 12 ≠ 9 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0,2,6,8,10,11] := remove (a 12) 9 [0,2,6,8,9,10,11] d12 b0
  have b1 : a 7 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t1 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b1
  have b2 : a 7 ≠ 3 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 3 d5 c20 (by decide +kernel)
  have t2 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t1 b2
  have b3 : a 14 ≠ 7 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,2,3,4,5,6,8,9,10,11] := remove (a 14) 7 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b3
  have b4 : a 14 ≠ 9 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 9 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,2,3,4,5,6,8,10,11] := remove (a 14) 9 [0,1,2,3,4,5,6,8,9,10,11] t3 b4
  have b5 : a 22 ≠ 2 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b5
  have b6 : a 22 ≠ 3 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,1,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 22 ≠ 4 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 22) 4 [0,1,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 22 ≠ 5 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,6,7,8,9,10,11] := remove (a 22) 5 [0,1,5,6,7,8,9,10,11] t7 b8
  have b9 : a 22 ≠ 7 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,6,8,9,10,11] := remove (a 22) 7 [0,1,6,7,8,9,10,11] t8 b9
  have b10 : a 22 ≠ 8 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,6,9,10,11] := remove (a 22) 8 [0,1,6,8,9,10,11] t9 b10
  have b11 : a 22 ≠ 9 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,6,10,11] := remove (a 22) 9 [0,1,6,9,10,11] t10 b11
  have b12 : a 22 ≠ 10 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,6,11] := remove (a 22) 10 [0,1,6,10,11] t11 b12
  have b13 : a 22 ≠ 11 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,6] := remove (a 22) 11 [0,1,6,11] t12 b13
  have b14 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 2 t2 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,3,4,5,6,7,8] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8] d15 b14
  have b15 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 t2 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,4,5,6,7,8] := remove (a 15) 3 [0,1,3,4,5,6,7,8] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t13 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,4,5,6,7,8])
    (d7 : a 7 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0,2,6,8,10,11])
    (d8 : a 8 ∈ [0,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 15 ∈ [0,1,4,5] ∧ a 23 ∈ [0,1,3,4] ∧ a 12 ∈ [0,6] ∧ a 24 ∈ [0,5,6,7,8,9,10,11] := by
  have b0 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 6 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,4,5,7,8] := remove (a 15) 6 [0,1,4,5,6,7,8] d15 b0
  have b1 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,4,5,8] := remove (a 15) 7 [0,1,4,5,7,8] t0 b1
  have b2 : a 15 ≠ 8 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,4,5] := remove (a 15) 8 [0,1,4,5,8] t1 b2
  have b3 : a 23 ≠ 2 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,3,4,5,6,7,8] := remove (a 23) 2 [0,1,2,3,4,5,6,7,8] d23 b3
  have b4 : a 23 ≠ 5 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,3,4,6,7,8] := remove (a 23) 5 [0,1,3,4,5,6,7,8] t3 b4
  have b5 : a 23 ≠ 6 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,3,4,7,8] := remove (a 23) 6 [0,1,3,4,6,7,8] t4 b5
  have b6 : a 23 ≠ 7 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,3,4,8] := remove (a 23) 7 [0,1,3,4,7,8] t5 b6
  have b7 : a 23 ≠ 8 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,3,4] := remove (a 23) 8 [0,1,3,4,8] t6 b7
  have b8 : a 12 ≠ 2 := exclude [0,3] (fun u v => edge r30 v u) (a 12) (a 8) 2 d8 c30 (by decide +kernel)
  have t8 : a 12 ∈ [0,6,8,10,11] := remove (a 12) 2 [0,2,6,8,10,11] d12 b8
  have b9 : a 12 ≠ 8 := exclude [0,3] (fun u v => edge r30 v u) (a 12) (a 8) 8 d8 c30 (by decide +kernel)
  have t9 : a 12 ∈ [0,6,10,11] := remove (a 12) 8 [0,6,8,10,11] t8 b9
  have b10 : a 12 ≠ 10 := exclude [0,3] (fun u v => edge r30 v u) (a 12) (a 8) 10 d8 c30 (by decide +kernel)
  have t10 : a 12 ∈ [0,6,11] := remove (a 12) 10 [0,6,10,11] t9 b10
  have b11 : a 12 ≠ 11 := exclude [0,3] (fun u v => edge r30 v u) (a 12) (a 8) 11 d8 c30 (by decide +kernel)
  have t11 : a 12 ∈ [0,6] := remove (a 12) 11 [0,6,11] t10 b11
  have b12 : a 24 ≠ 1 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b12
  have b13 : a 24 ≠ 2 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 24 ≠ 3 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 24 ≠ 4 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,5,6,7,8,9,10,11] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t7 (And.intro t11 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,3])
    (d13 : a 13 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,4])
    (d11 : a 11 ∈ [0,4,5,6])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,8,10,11])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    : a 24 ∈ [0,9] ∧ a 13 ∈ [0,1] ∧ a 25 ∈ [0,2,4,5,6,7,8] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0,6] ∧ a 14 ∈ [0,5,6,8,10,11] := by
  have b0 : a 24 ≠ 5 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,6,7,8,9,10,11] := remove (a 24) 5 [0,5,6,7,8,9,10,11] d24 b0
  have b1 : a 24 ≠ 6 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,7,8,9,10,11] := remove (a 24) 6 [0,6,7,8,9,10,11] t0 b1
  have b2 : a 24 ≠ 7 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,8,9,10,11] := remove (a 24) 7 [0,7,8,9,10,11] t1 b2
  have b3 : a 24 ≠ 8 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,9,10,11] := remove (a 24) 8 [0,8,9,10,11] t2 b3
  have b4 : a 24 ≠ 10 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,9,11] := remove (a 24) 10 [0,9,10,11] t3 b4
  have b5 : a 24 ≠ 11 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,9] := remove (a 24) 11 [0,9,11] t4 b5
  have b6 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t6 : a 13 ∈ [0,1] := remove (a 13) 2 [0,1,2] d13 b6
  have b7 : a 25 ≠ 1 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,2,3,4,5,6,7,8] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8] d25 b7
  have b8 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,4,5,6,7,8] := remove (a 25) 3 [0,2,3,4,5,6,7,8] t7 b8
  have b9 : a 10 ≠ 4 := exclude [0,4,5,6] (edge r35) (a 10) (a 11) 4 d11 c35 (by decide +kernel)
  have t9 : a 10 ∈ [0] := remove (a 10) 4 [0,4] d10 b9
  have b10 : a 11 ≠ 4 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 4 t9 c35 (by decide +kernel)
  have t10 : a 11 ∈ [0,5,6] := remove (a 11) 4 [0,4,5,6] d11 b10
  have b11 : a 11 ≠ 5 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 5 t9 c35 (by decide +kernel)
  have t11 : a 11 ∈ [0,6] := remove (a 11) 5 [0,5,6] t10 b11
  have b12 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 t9 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0,2,3,4,5,6,8,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,8,10,11] d14 b12
  have b13 : a 14 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 2 t9 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,3,4,5,6,8,10,11] := remove (a 14) 2 [0,2,3,4,5,6,8,10,11] t12 b13
  have b14 : a 14 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 3 t9 c36 (by decide +kernel)
  have t14 : a 14 ∈ [0,4,5,6,8,10,11] := remove (a 14) 3 [0,3,4,5,6,8,10,11] t13 b14
  have b15 : a 14 ≠ 4 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 4 t9 c36 (by decide +kernel)
  have t15 : a 14 ∈ [0,5,6,8,10,11] := remove (a 14) 4 [0,4,5,6,8,10,11] t14 b15
  exact And.intro t5 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t11 (t15)))))

theorem chunk7 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,5,6,8,10,11])
    (d10 : a 10 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1,4,5])
    (d11 : a 11 ∈ [0,6])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 14 ∈ [0] ∧ a 26 ∈ [0,2] ∧ a 15 ∈ [0,4,5] := by
  have b0 : a 14 ≠ 5 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,6,8,10,11] := remove (a 14) 5 [0,5,6,8,10,11] d14 b0
  have b1 : a 14 ≠ 6 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 6 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,8,10,11] := remove (a 14) 6 [0,6,8,10,11] t0 b1
  have b2 : a 14 ≠ 8 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 8 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,10,11] := remove (a 14) 8 [0,8,10,11] t1 b2
  have b3 : a 14 ≠ 10 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 10 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,11] := remove (a 14) 10 [0,10,11] t2 b3
  have b4 : a 14 ≠ 11 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0] := remove (a 14) 11 [0,11] t3 b4
  have b5 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b5
  have b6 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 26) 3 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 26) 4 [0,2,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,2,6,7,8,9,10,11] := remove (a 26) 5 [0,2,5,6,7,8,9,10,11] t7 b8
  have b9 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,7,8,9,10,11] := remove (a 26) 6 [0,2,6,7,8,9,10,11] t8 b9
  have b10 : a 26 ≠ 7 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,2,8,9,10,11] := remove (a 26) 7 [0,2,7,8,9,10,11] t9 b10
  have b11 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,9,10,11] := remove (a 26) 8 [0,2,8,9,10,11] t10 b11
  have b12 : a 26 ≠ 9 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,10,11] := remove (a 26) 9 [0,2,9,10,11] t11 b12
  have b13 : a 26 ≠ 10 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,11] := remove (a 26) 10 [0,2,10,11] t12 b13
  have b14 : a 26 ≠ 11 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,2] := remove (a 26) 11 [0,2,11] t13 b14
  have b15 : a 15 ≠ 1 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0,4,5] := remove (a 15) 1 [0,1,4,5] d15 b15
  exact And.intro t4 (And.intro t14 (t15))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_203
