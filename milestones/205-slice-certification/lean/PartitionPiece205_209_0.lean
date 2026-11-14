import PartitionData205_209
namespace PartitionCover205_209
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    : a 2 ∈ [0,2] ∧ a 5 ∈ [0,2] ∧ a 9 ∈ [0,2] ∧ a 17 ∈ [0,2] ∧ a 3 ∈ [0,2] ∧ a 6 ∈ [0,2] ∧ a 18 ∈ [0,2,6,7,8,9] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b2
  have b3 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t2 b3
  have b4 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b4
  have b5 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t4 b5
  have b6 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t6 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b6
  have b7 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t6 b7
  have b8 : a 3 ≠ 1 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 1 t1 c9 (by decide +kernel)
  have t8 : a 3 ∈ [0,2,3] := remove (a 3) 1 [0,1,2,3] d3 b8
  have b9 : a 3 ≠ 3 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 3 t1 c9 (by decide +kernel)
  have t9 : a 3 ∈ [0,2] := remove (a 3) 3 [0,2,3] t8 b9
  have b10 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 1 t1 c10 (by decide +kernel)
  have t10 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b10
  have b11 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 6) (a 2) 3 t1 c10 (by decide +kernel)
  have t11 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t10 b11
  have b12 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 1 t1 c12 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9] d18 b12
  have b13 : a 18 ≠ 3 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 3 t1 c12 (by decide +kernel)
  have t13 : a 18 ∈ [0,2,4,5,6,7,8,9] := remove (a 18) 3 [0,2,3,4,5,6,7,8,9] t12 b13
  have b14 : a 18 ≠ 4 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 4 t1 c12 (by decide +kernel)
  have t14 : a 18 ∈ [0,2,5,6,7,8,9] := remove (a 18) 4 [0,2,4,5,6,7,8,9] t13 b14
  have b15 : a 18 ≠ 5 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 5 t1 c12 (by decide +kernel)
  have t15 : a 18 ∈ [0,2,6,7,8,9] := remove (a 18) 5 [0,2,5,6,7,8,9] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2,6,7,8,9])
    (d2 : a 2 ∈ [0,2])
    (d7 : a 7 ∈ [0,1,2])
    (d3 : a 3 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,2])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8])
    (d24 : a 24 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 18 ∈ [0,2] ∧ a 7 ∈ [0,2] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0,2] ∧ a 22 ∈ [0,1,3,4] ∧ a 23 ∈ [0,1,2,6,7,8] ∧ a 24 ∈ [0,2,5] := by
  have b0 : a 18 ≠ 6 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t0 : a 18 ∈ [0,2,7,8,9] := remove (a 18) 6 [0,2,6,7,8,9] d18 b0
  have b1 : a 18 ≠ 7 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 7 d2 c12 (by decide +kernel)
  have t1 : a 18 ∈ [0,2,8,9] := remove (a 18) 7 [0,2,7,8,9] t0 b1
  have b2 : a 18 ≠ 8 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 8 d2 c12 (by decide +kernel)
  have t2 : a 18 ∈ [0,2,9] := remove (a 18) 8 [0,2,8,9] t1 b2
  have b3 : a 18 ≠ 9 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,2] := remove (a 18) 9 [0,2,9] t2 b3
  have b4 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 1 d3 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0,2] := remove (a 7) 1 [0,1,2] d7 b4
  have b5 : a 19 ≠ 1 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b5
  have b6 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b6
  have b7 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] t6 b7
  have b8 : a 22 ≠ 2 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,3,4,5] := remove (a 22) 2 [0,1,2,3,4,5] d22 b8
  have b9 : a 22 ≠ 5 := exclude [0,2] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,3,4] := remove (a 22) 5 [0,1,3,4,5] t8 b9
  have b10 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 3 t4 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,2,4,5,6,7,8] := remove (a 23) 3 [0,1,2,3,4,5,6,7,8] d23 b10
  have b11 : a 23 ≠ 4 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 4 t4 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2,5,6,7,8] := remove (a 23) 4 [0,1,2,4,5,6,7,8] t10 b11
  have b12 : a 23 ≠ 5 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 5 t4 c27 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,6,7,8] := remove (a 23) 5 [0,1,2,5,6,7,8] t11 b12
  have b13 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,2,3,4,5] := remove (a 24) 1 [0,1,2,3,4,5] d24 b13
  have b14 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,4,5] := remove (a 24) 3 [0,2,3,4,5] t13 b14
  have b15 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,2,5] := remove (a 24) 4 [0,2,4,5] t14 b15
  exact And.intro t3 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t12 (t15))))))

theorem chunk2 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2,5])
    (d8 : a 8 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0])
    (d18 : a 18 ∈ [0,2])
    (d19 : a 19 ∈ [0])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    : a 24 ∈ [0,2] ∧ a 11 ∈ [0,2] ∧ a 26 ∈ [0,1] ∧ a 15 ∈ [0,2] ∧ a 29 ∈ [0,2] ∧ a 18 ∈ [0] := by
  have b0 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,2] := remove (a 24) 5 [0,2,5] d24 b0
  have b1 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 1 d9 c32 (by decide +kernel)
  have t1 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b1
  have b2 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t2 : a 11 ∈ [0,2] := remove (a 11) 3 [0,2,3] t1 b2
  have b3 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8,9] d26 b3
  have b4 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,4,5,6,7,8,9] := remove (a 26) 3 [0,1,3,4,5,6,7,8,9] t3 b4
  have b5 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,5,6,7,8,9] := remove (a 26) 4 [0,1,4,5,6,7,8,9] t4 b5
  have b6 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,6,7,8,9] := remove (a 26) 5 [0,1,5,6,7,8,9] t5 b6
  have b7 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,7,8,9] := remove (a 26) 6 [0,1,6,7,8,9] t6 b7
  have b8 : a 26 ≠ 7 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,8,9] := remove (a 26) 7 [0,1,7,8,9] t7 b8
  have b9 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,9] := remove (a 26) 8 [0,1,8,9] t8 b9
  have b10 : a 26 ≠ 9 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0,1] := remove (a 26) 9 [0,1,9] t9 b10
  have b11 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r38 v u) (a 15) (a 11) 1 t2 c38 (by decide +kernel)
  have t11 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b11
  have b12 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r38 v u) (a 15) (a 11) 3 t2 c38 (by decide +kernel)
  have t12 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t13 b14
  have b15 : a 18 ≠ 2 := exclude [0] (edge r55) (a 18) (a 19) 2 d19 c55 (by decide +kernel)
  have t15 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b15
  exact And.intro t0 (And.intro t2 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,3,4])
    (d18 : a 18 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,6,7,8])
    (d19 : a 19 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d21 : a 21 ∈ [0,2])
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 22 ∈ [0,3] ∧ a 23 ∈ [0,6] ∧ a 27 ∈ [0,1] := by
  have b0 : a 22 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t0 : a 22 ∈ [0,3,4] := remove (a 22) 1 [0,1,3,4] d22 b0
  have b1 : a 22 ≠ 4 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t1 : a 22 ∈ [0,3] := remove (a 22) 4 [0,3,4] t0 b1
  have b2 : a 23 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,2,6,7,8] := remove (a 23) 1 [0,1,2,6,7,8] d23 b2
  have b3 : a 23 ≠ 7 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,2,6,8] := remove (a 23) 7 [0,2,6,7,8] t2 b3
  have b4 : a 27 ≠ 2 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 2 d19 c59 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b4
  have b5 : a 27 ≠ 3 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 3 d19 c59 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 27 ≠ 4 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 4 d19 c59 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 27 ≠ 5 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 5 d19 c59 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 27 ≠ 6 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 6 d19 c59 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,7,8,9,10,11] := remove (a 27) 6 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 27 ≠ 7 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 7 d19 c59 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,8,9,10,11] := remove (a 27) 7 [0,1,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 8 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 8 d19 c59 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,9,10,11] := remove (a 27) 8 [0,1,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 9 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 9 d19 c59 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,10,11] := remove (a 27) 9 [0,1,9,10,11] t10 b11
  have b12 : a 27 ≠ 10 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 10 d19 c59 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,11] := remove (a 27) 10 [0,1,10,11] t11 b12
  have b13 : a 27 ≠ 11 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 11 d19 c59 (by decide +kernel)
  have t13 : a 27 ∈ [0,1] := remove (a 27) 11 [0,1,11] t12 b13
  have b14 : a 23 ≠ 2 := exclude [0,2] (fun u v => edge r63 v u) (a 23) (a 21) 2 d21 c63 (by decide +kernel)
  have t14 : a 23 ∈ [0,6,8] := remove (a 23) 2 [0,2,6,8] t3 b14
  have b15 : a 23 ≠ 8 := exclude [0,2] (fun u v => edge r63 v u) (a 23) (a 21) 8 d21 c63 (by decide +kernel)
  have t15 : a 23 ∈ [0,6] := remove (a 23) 8 [0,6,8] t14 b15
  exact And.intro t1 (And.intro t15 (t13))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_209
