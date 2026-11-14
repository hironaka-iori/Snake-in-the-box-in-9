import PartitionData205_196
namespace PartitionCover205_196
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,3,4,5])
    (d6 : a 6 ∈ [0,1,3,5])
    (d22 : a 22 ∈ [0,1,2])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2,4])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 14 ∈ [0,2,4] ∧ a 22 ∈ [0,1] ∧ a 15 ∈ [0,1,2,4] ∧ a 23 ∈ [0,1,2,4] ∧ a 8 ∈ [0,2] ∧ a 10 ∈ [0,1,2,3] ∧ a 24 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 14 ≠ 3 := exclude [0,1,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,4,5] := remove (a 14) 3 [0,2,3,4,5] d14 b0
  have b1 : a 14 ≠ 5 := exclude [0,1,3,5] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,4] := remove (a 14) 5 [0,2,4,5] t0 b1
  have b2 : a 22 ≠ 2 := exclude [0,1,3,5] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,1] := remove (a 22) 2 [0,1,2] d22 b2
  have b3 : a 15 ≠ 3 := exclude [0,1,2,4] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,4,5] := remove (a 15) 3 [0,1,2,3,4,5] d15 b3
  have b4 : a 15 ≠ 5 := exclude [0,1,2,4] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,2,4] := remove (a 15) 5 [0,1,2,4,5] t3 b4
  have b5 : a 23 ≠ 3 := exclude [0,1,2,4] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,2,4,5] := remove (a 23) 3 [0,1,2,3,4,5] d23 b5
  have b6 : a 23 ≠ 5 := exclude [0,1,2,4] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,2,4] := remove (a 23) 5 [0,1,2,4,5] t5 b6
  have b7 : a 8 ≠ 1 := exclude [0,2] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t7 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b7
  have b8 : a 8 ≠ 3 := exclude [0,2] (edge r28) (a 8) (a 9) 3 d9 c28 (by decide +kernel)
  have t8 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t7 b8
  have b9 : a 10 ≠ 4 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 4 t8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,2,3,5] := remove (a 10) 4 [0,1,2,3,4,5] d10 b9
  have b10 : a 10 ≠ 5 := exclude [0,2] (fun u v => edge r29 v u) (a 10) (a 8) 5 t8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0,1,2,3] := remove (a 10) 5 [0,1,2,3,5] t9 b10
  have b11 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 1 t8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b11
  have b12 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 2 t8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 3 t8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 24 ≠ 4 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 4 t8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 24 ≠ 5 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 5 t8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (t15))))))

theorem chunk5 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17])
    (d8 : a 8 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,4,5,7,8])
    (d9 : a 9 ∈ [0,2])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 24 ∈ [0,6,12,14] ∧ a 11 ∈ [0,1,4,5] ∧ a 25 ∈ [0,1,3,5,7,9,11] := by
  have b0 : a 24 ≠ 7 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] d24 b0
  have b1 : a 24 ≠ 8 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 24) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 24 ≠ 9 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 24) 9 [0,6,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 24 ≠ 10 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 24) 10 [0,6,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 24 ≠ 11 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,6,12,13,14,15,16,17] := remove (a 24) 11 [0,6,11,12,13,14,15,16,17] t3 b4
  have b5 : a 24 ≠ 13 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,6,12,14,15,16,17] := remove (a 24) 13 [0,6,12,13,14,15,16,17] t4 b5
  have b6 : a 24 ≠ 15 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,6,12,14,16,17] := remove (a 24) 15 [0,6,12,14,15,16,17] t5 b6
  have b7 : a 24 ≠ 16 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 16 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,6,12,14,17] := remove (a 24) 16 [0,6,12,14,16,17] t6 b7
  have b8 : a 24 ≠ 17 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,6,12,14] := remove (a 24) 17 [0,6,12,14,17] t7 b8
  have b9 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 7 d9 c32 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,4,5,8] := remove (a 11) 7 [0,1,4,5,7,8] d11 b9
  have b10 : a 11 ≠ 8 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 8 d9 c32 (by decide +kernel)
  have t10 : a 11 ∈ [0,1,4,5] := remove (a 11) 8 [0,1,4,5,8] t9 b10
  have b11 : a 25 ≠ 2 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b11
  have b12 : a 25 ≠ 4 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,3,5,6,7,8,9,10,11] := remove (a 25) 4 [0,1,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 25 ≠ 6 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,3,5,7,8,9,10,11] := remove (a 25) 6 [0,1,3,5,6,7,8,9,10,11] t12 b13
  have b14 : a 25 ≠ 8 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,3,5,7,9,10,11] := remove (a 25) 8 [0,1,3,5,7,8,9,10,11] t13 b14
  have b15 : a 25 ≠ 10 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,3,5,7,9,11] := remove (a 25) 10 [0,1,3,5,7,9,10,11] t14 b15
  exact And.intro t8 (And.intro t10 (t15))

theorem chunk6 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,3,5,7,9,11])
    (d9 : a 9 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1,4,5])
    (d14 : a 14 ∈ [0,2,4])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 25 ∈ [0,1,3,5,7,9] ∧ a 10 ∈ [0,1] ∧ a 11 ∈ [0,4] ∧ a 14 ∈ [0,2] ∧ a 26 ∈ [0,1,10,11,12,13,16,17,18,19,20,21,22,23] := by
  have b0 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,3,5,7,9] := remove (a 25) 11 [0,1,3,5,7,9,11] d25 b0
  have b1 : a 10 ≠ 2 := exclude [0,1,4,5] (edge r35) (a 10) (a 11) 2 d11 c35 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,3] := remove (a 10) 2 [0,1,2,3] d10 b1
  have b2 : a 10 ≠ 3 := exclude [0,1,4,5] (edge r35) (a 10) (a 11) 3 d11 c35 (by decide +kernel)
  have t2 : a 10 ∈ [0,1] := remove (a 10) 3 [0,1,3] t1 b2
  have b3 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r35 v u) (a 11) (a 10) 1 t2 c35 (by decide +kernel)
  have t3 : a 11 ∈ [0,4,5] := remove (a 11) 1 [0,1,4,5] d11 b3
  have b4 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r35 v u) (a 11) (a 10) 5 t2 c35 (by decide +kernel)
  have t4 : a 11 ∈ [0,4] := remove (a 11) 5 [0,4,5] t3 b4
  have b5 : a 14 ≠ 4 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 4 t2 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,2] := remove (a 14) 4 [0,2,4] d14 b5
  have b6 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 2 t2 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d26 b6
  have b7 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 3 t2 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 26 ≠ 4 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 4 t2 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 5 t2 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 26 ≠ 6 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 6 t2 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 26 ≠ 7 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 7 t2 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 26 ≠ 8 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 8 t2 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 26 ≠ 9 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 9 t2 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 26) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 26 ≠ 14 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 14 t2 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,10,11,12,13,15,16,17,18,19,20,21,22,23] := remove (a 26) 14 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 26 ≠ 15 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 15 t2 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,10,11,12,13,16,17,18,19,20,21,22,23] := remove (a 26) 15 [0,1,10,11,12,13,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t5 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,10,11,12,13,16,17,18,19,20,21,22,23])
    (d10 : a 10 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,4])
    (d12 : a 12 ∈ [0,2,6,10])
    (d13 : a 13 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 26 ∈ [0,1,10,11,12,13,18,19,20,22] ∧ a 27 ∈ [0,1,7] ∧ a 12 ∈ [0,2] ∧ a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 26 ≠ 16 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 16 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,10,11,12,13,17,18,19,20,21,22,23] := remove (a 26) 16 [0,1,10,11,12,13,16,17,18,19,20,21,22,23] d26 b0
  have b1 : a 26 ≠ 17 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 17 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,10,11,12,13,18,19,20,21,22,23] := remove (a 26) 17 [0,1,10,11,12,13,17,18,19,20,21,22,23] t0 b1
  have b2 : a 26 ≠ 21 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 21 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,10,11,12,13,18,19,20,22,23] := remove (a 26) 21 [0,1,10,11,12,13,18,19,20,21,22,23] t1 b2
  have b3 : a 26 ≠ 23 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 23 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,10,11,12,13,18,19,20,22] := remove (a 26) 23 [0,1,10,11,12,13,18,19,20,22,23] t2 b3
  have b4 : a 27 ≠ 2 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b4
  have b5 : a 27 ≠ 3 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 27 ≠ 4 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 27 ≠ 5 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 27 ≠ 6 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,7,8,9,10,11] := remove (a 27) 6 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 27 ≠ 8 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,7,9,10,11] := remove (a 27) 8 [0,1,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 9 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,7,10,11] := remove (a 27) 9 [0,1,7,9,10,11] t9 b10
  have b11 : a 27 ≠ 10 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,7,11] := remove (a 27) 10 [0,1,7,10,11] t10 b11
  have b12 : a 27 ≠ 11 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,7] := remove (a 27) 11 [0,1,7,11] t11 b12
  have b13 : a 12 ≠ 6 := exclude [0,2] (edge r40) (a 12) (a 13) 6 d13 c40 (by decide +kernel)
  have t13 : a 12 ∈ [0,2,10] := remove (a 12) 6 [0,2,6,10] d12 b13
  have b14 : a 12 ≠ 10 := exclude [0,2] (edge r40) (a 12) (a 13) 10 d13 c40 (by decide +kernel)
  have t14 : a 12 ∈ [0,2] := remove (a 12) 10 [0,2,10] t13 b14
  have b15 : a 28 ≠ 1 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 1 t14 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b15
  exact And.intro t3 (And.intro t12 (And.intro t14 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_196
