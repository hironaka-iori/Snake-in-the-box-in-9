import PartitionData205_211
namespace PartitionCover205_211
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,3,4,5,6,7,8])
    (d6 : a 6 ∈ [0,1,6,7])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2,4])
    (d10 : a 10 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,3])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    : a 14 ∈ [0,1,3,4] ∧ a 22 ∈ [0,1,6,7] ∧ a 23 ∈ [0,1,2,4] ∧ a 10 ∈ [0,2] := by
  have b0 : a 14 ≠ 5 := exclude [0,1,6,7] (fun u v => edge r24 v u) (a 14) (a 6) 5 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,3,4,6,7,8] := remove (a 14) 5 [0,1,3,4,5,6,7,8] d14 b0
  have b1 : a 14 ≠ 6 := exclude [0,1,6,7] (fun u v => edge r24 v u) (a 14) (a 6) 6 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,3,4,7,8] := remove (a 14) 6 [0,1,3,4,6,7,8] t0 b1
  have b2 : a 14 ≠ 7 := exclude [0,1,6,7] (fun u v => edge r24 v u) (a 14) (a 6) 7 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,3,4,8] := remove (a 14) 7 [0,1,3,4,7,8] t1 b2
  have b3 : a 14 ≠ 8 := exclude [0,1,6,7] (fun u v => edge r24 v u) (a 14) (a 6) 8 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,3,4] := remove (a 14) 8 [0,1,3,4,8] t2 b3
  have b4 : a 22 ≠ 2 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 22) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b4
  have b5 : a 22 ≠ 3 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 22) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 22 ≠ 4 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 22) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 22 ≠ 5 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,1,6,7,8,9,10,11] := remove (a 22) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 22 ≠ 8 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,6,7,9,10,11] := remove (a 22) 8 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 22 ≠ 9 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,6,7,10,11] := remove (a 22) 9 [0,1,6,7,9,10,11] t8 b9
  have b10 : a 22 ≠ 10 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,6,7,11] := remove (a 22) 10 [0,1,6,7,10,11] t9 b10
  have b11 : a 22 ≠ 11 := exclude [0,1,6,7] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,6,7] := remove (a 22) 11 [0,1,6,7,11] t10 b11
  have b12 : a 23 ≠ 3 := exclude [0,1,2,4] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,4,5] := remove (a 23) 3 [0,1,2,3,4,5] d23 b12
  have b13 : a 23 ≠ 5 := exclude [0,1,2,4] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,2,4] := remove (a 23) 5 [0,1,2,4,5] t12 b13
  have b14 : a 10 ≠ 1 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 1 d8 c29 (by decide +kernel)
  have t14 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b14
  have b15 : a 10 ≠ 3 := exclude [0,3] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t15 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t14 b15
  exact And.intro t3 (And.intro t11 (And.intro t13 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d8 : a 8 ∈ [0,3])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,1,6,7])
    (d13 : a 13 ∈ [0,3,6,8])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 24 ∈ [0,2] ∧ a 11 ∈ [0,1,2,4] ∧ a 9 ∈ [0,6] ∧ a 25 ∈ [0,3] := by
  have b0 : a 24 ≠ 1 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9] d24 b0
  have b1 : a 24 ≠ 3 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,4,5,6,7,8,9] := remove (a 24) 3 [0,2,3,4,5,6,7,8,9] t0 b1
  have b2 : a 24 ≠ 4 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,2,5,6,7,8,9] := remove (a 24) 4 [0,2,4,5,6,7,8,9] t1 b2
  have b3 : a 24 ≠ 5 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,2,6,7,8,9] := remove (a 24) 5 [0,2,5,6,7,8,9] t2 b3
  have b4 : a 24 ≠ 6 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,2,7,8,9] := remove (a 24) 6 [0,2,6,7,8,9] t3 b4
  have b5 : a 24 ≠ 7 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,2,8,9] := remove (a 24) 7 [0,2,7,8,9] t4 b5
  have b6 : a 24 ≠ 8 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,9] := remove (a 24) 8 [0,2,8,9] t5 b6
  have b7 : a 24 ≠ 9 := exclude [0,3] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,2] := remove (a 24) 9 [0,2,9] t6 b7
  have b8 : a 11 ≠ 3 := exclude [0,1,6,7] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,2,4,5] := remove (a 11) 3 [0,1,2,3,4,5] d11 b8
  have b9 : a 11 ≠ 5 := exclude [0,1,6,7] (fun u v => edge r32 v u) (a 11) (a 9) 5 d9 c32 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,2,4] := remove (a 11) 5 [0,1,2,4,5] t8 b9
  have b10 : a 9 ≠ 1 := exclude [0,3,6,8] (edge r33) (a 9) (a 13) 1 d13 c33 (by decide +kernel)
  have t10 : a 9 ∈ [0,6,7] := remove (a 9) 1 [0,1,6,7] d9 b10
  have b11 : a 9 ≠ 7 := exclude [0,3,6,8] (edge r33) (a 9) (a 13) 7 d13 c33 (by decide +kernel)
  have t11 : a 9 ∈ [0,6] := remove (a 9) 7 [0,6,7] t10 b11
  have b12 : a 25 ≠ 1 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 1 t11 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,2,3,4,5] := remove (a 25) 1 [0,1,2,3,4,5] d25 b12
  have b13 : a 25 ≠ 2 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 2 t11 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,3,4,5] := remove (a 25) 2 [0,2,3,4,5] t12 b13
  have b14 : a 25 ≠ 4 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 4 t11 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,3,5] := remove (a 25) 4 [0,3,4,5] t13 b14
  have b15 : a 25 ≠ 5 := exclude [0,6] (fun u v => edge r34 v u) (a 25) (a 9) 5 t11 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,3] := remove (a 25) 5 [0,3,5] t14 b15
  exact And.intro t7 (And.intro t9 (And.intro t11 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,2,4])
    (d10 : a 10 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,3,4])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d15 : a 15 ∈ [0,1,2])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 11 ∈ [0,1] ∧ a 14 ∈ [0,3] ∧ a 26 ∈ [0,1,3,4,6,7,9] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,1,6,7] := by
  have b0 : a 11 ≠ 2 := exclude [0,2] (fun u v => edge r35 v u) (a 11) (a 10) 2 d10 c35 (by decide +kernel)
  have t0 : a 11 ∈ [0,1,4] := remove (a 11) 2 [0,1,2,4] d11 b0
  have b1 : a 11 ≠ 4 := exclude [0,2] (fun u v => edge r35 v u) (a 11) (a 10) 4 d10 c35 (by decide +kernel)
  have t1 : a 11 ∈ [0,1] := remove (a 11) 4 [0,1,4] t0 b1
  have b2 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,3,4] := remove (a 14) 1 [0,1,3,4] d14 b2
  have b3 : a 14 ≠ 4 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,3] := remove (a 14) 4 [0,3,4] t2 b3
  have b4 : a 26 ≠ 2 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8,9] d26 b4
  have b5 : a 26 ≠ 5 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,3,4,6,7,8,9] := remove (a 26) 5 [0,1,3,4,5,6,7,8,9] t4 b5
  have b6 : a 26 ≠ 8 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,3,4,6,7,9] := remove (a 26) 8 [0,1,3,4,6,7,8,9] t5 b6
  have b7 : a 15 ≠ 2 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 2 t1 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,1] := remove (a 15) 2 [0,1,2] d15 b7
  have b8 : a 27 ≠ 2 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 2 t1 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b8
  have b9 : a 27 ≠ 3 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 3 t1 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 4 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 4 t1 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 5 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 5 t1 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 8 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 8 t1 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,6,7,9,10,11] := remove (a 27) 8 [0,1,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 9 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 9 t1 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,6,7,10,11] := remove (a 27) 9 [0,1,6,7,9,10,11] t12 b13
  have b14 : a 27 ≠ 10 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 10 t1 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,6,7,11] := remove (a 27) 10 [0,1,6,7,10,11] t13 b14
  have b15 : a 27 ≠ 11 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 11 t1 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,6,7] := remove (a 27) 11 [0,1,6,7,11] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t6 (And.intro t7 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,2])
    (d13 : a 13 ∈ [0,3,6,8])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 12 ∈ [0] ∧ a 13 ∈ [0,3] ∧ a 28 ∈ [0,9] ∧ a 29 ∈ [0,2,5,6,7,8,9] := by
  have b0 : a 12 ≠ 2 := exclude [0,3,6,8] (edge r40) (a 12) (a 13) 2 d13 c40 (by decide +kernel)
  have t0 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b0
  have b1 : a 13 ≠ 6 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 6 t0 c40 (by decide +kernel)
  have t1 : a 13 ∈ [0,3,8] := remove (a 13) 6 [0,3,6,8] d13 b1
  have b2 : a 13 ≠ 8 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 8 t0 c40 (by decide +kernel)
  have t2 : a 13 ∈ [0,3] := remove (a 13) 8 [0,3,8] t1 b2
  have b3 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t0 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b3
  have b4 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 t0 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 28) 2 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 t0 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 28) 3 [0,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 t0 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,5,6,7,8,9,10,11] := remove (a 28) 4 [0,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 t0 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,6,7,8,9,10,11] := remove (a 28) 5 [0,5,6,7,8,9,10,11] t6 b7
  have b8 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 t0 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,7,8,9,10,11] := remove (a 28) 6 [0,6,7,8,9,10,11] t7 b8
  have b9 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 t0 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,8,9,10,11] := remove (a 28) 7 [0,7,8,9,10,11] t8 b9
  have b10 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 t0 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,9,10,11] := remove (a 28) 8 [0,8,9,10,11] t9 b10
  have b11 : a 28 ≠ 10 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 10 t0 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,9,11] := remove (a 28) 10 [0,9,10,11] t10 b11
  have b12 : a 28 ≠ 11 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 11 t0 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,9] := remove (a 28) 11 [0,9,11] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 1 t2 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 3 t2 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,2,4,5,6,7,8,9] := remove (a 29) 3 [0,2,3,4,5,6,7,8,9] t13 b14
  have b15 : a 29 ≠ 4 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 4 t2 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,5,6,7,8,9] := remove (a 29) 4 [0,2,4,5,6,7,8,9] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t12 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_211
