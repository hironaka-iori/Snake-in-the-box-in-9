import PartitionData205_195
namespace PartitionCover205_195
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d9 : a 9 ∈ [0,1,2])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0,1,2,3])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    : a 2 ∈ [0,2] ∧ a 16 ∈ [0,1,10,11,12,13,18,19] ∧ a 9 ∈ [0,2] ∧ a 3 ∈ [0,2,3] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d16 b2
  have b3 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t2 b3
  have b4 : a 16 ≠ 4 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 4 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t3 b4
  have b5 : a 16 ≠ 5 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 5 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t4 b5
  have b6 : a 16 ≠ 6 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 6 d0 c4 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t5 b6
  have b7 : a 16 ≠ 7 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 7 d0 c4 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19] t6 b7
  have b8 : a 16 ≠ 8 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 8 d0 c4 (by decide +kernel)
  have t8 : a 16 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19] t7 b8
  have b9 : a 16 ≠ 9 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 9 d0 c4 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,10,11,12,13,14,15,16,17,18,19] := remove (a 16) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 16 ≠ 14 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 14 d0 c4 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,10,11,12,13,15,16,17,18,19] := remove (a 16) 14 [0,1,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 16 ≠ 15 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 15 d0 c4 (by decide +kernel)
  have t11 : a 16 ∈ [0,1,10,11,12,13,16,17,18,19] := remove (a 16) 15 [0,1,10,11,12,13,15,16,17,18,19] t10 b11
  have b12 : a 16 ≠ 16 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 16 d0 c4 (by decide +kernel)
  have t12 : a 16 ∈ [0,1,10,11,12,13,17,18,19] := remove (a 16) 16 [0,1,10,11,12,13,16,17,18,19] t11 b12
  have b13 : a 16 ≠ 17 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 17 d0 c4 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,10,11,12,13,18,19] := remove (a 16) 17 [0,1,10,11,12,13,17,18,19] t12 b13
  have b14 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t14 : a 9 ∈ [0,2] := remove (a 9) 1 [0,1,2] d9 b14
  have b15 : a 3 ≠ 1 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 1 t1 c9 (by decide +kernel)
  have t15 : a 3 ∈ [0,2,3] := remove (a 3) 1 [0,1,2,3] d3 b15
  exact And.intro t1 (And.intro t13 (And.intro t14 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2,3])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1,2,3,4,5,6,7])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    : a 3 ∈ [0,2] ∧ a 10 ∈ [0,3] ∧ a 18 ∈ [0,4,5,7,8,11] ∧ a 7 ∈ [0,2] ∧ a 11 ∈ [0,2,4,6] ∧ a 19 ∈ [0,1,2,3,4,5,6,8,9,10,11,12,13] := by
  have b0 : a 3 ≠ 3 := exclude [0,2] (fun u v => edge r9 v u) (a 3) (a 2) 3 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0,2] := remove (a 3) 3 [0,2,3] d3 b0
  have b1 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b1
  have b2 : a 10 ≠ 2 := exclude [0,2] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,3] := remove (a 10) 2 [0,2,3] t1 b2
  have b3 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 18) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b3
  have b4 : a 18 ≠ 2 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 2 d2 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 18) 2 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 18 ≠ 3 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 3 d2 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 18) 3 [0,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 18 ≠ 6 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 6 d2 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0,4,5,7,8,9,10,11] := remove (a 18) 6 [0,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 18 ≠ 9 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 9 d2 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0,4,5,7,8,10,11] := remove (a 18) 9 [0,4,5,7,8,9,10,11] t6 b7
  have b8 : a 18 ≠ 10 := exclude [0,2] (fun u v => edge r12 v u) (a 18) (a 2) 10 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0,4,5,7,8,11] := remove (a 18) 10 [0,4,5,7,8,10,11] t7 b8
  have b9 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 1 t0 c13 (by decide +kernel)
  have t9 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b9
  have b10 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 3 t0 c13 (by decide +kernel)
  have t10 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t9 b10
  have b11 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 1 t0 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,2,3,4,5,6,7] := remove (a 11) 1 [0,1,2,3,4,5,6,7] d11 b11
  have b12 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 3 t0 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,2,4,5,6,7] := remove (a 11) 3 [0,2,3,4,5,6,7] t11 b12
  have b13 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 5 t0 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,4,6,7] := remove (a 11) 5 [0,2,4,5,6,7] t12 b13
  have b14 : a 11 ≠ 7 := exclude [0,2] (fun u v => edge r14 v u) (a 11) (a 3) 7 t0 c14 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,4,6] := remove (a 11) 7 [0,2,4,6,7] t13 b14
  have b15 : a 19 ≠ 7 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 7 t0 c15 (by decide +kernel)
  have t15 : a 19 ∈ [0,1,2,3,4,5,6,8,9,10,11,12,13] := remove (a 19) 7 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d19 b15
  exact And.intro t0 (And.intro t2 (And.intro t8 (And.intro t10 (And.intro t14 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,8,9,10,11,12,13])
    (d3 : a 3 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d9 : a 9 ∈ [0,2])
    (c15 : edge r15 (a 3) (a 19)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 19 ∈ [0,1,2,3,4,5,6,8,9,10,11,12] ∧ a 14 ∈ [0,2] ∧ a 23 ∈ [0,2] ∧ a 24 ∈ [0,2,3,8] ∧ a 25 ∈ [0,1,2,3,4,6,8,9,10,12,13,14,15,16,17] := by
  have b0 : a 19 ≠ 13 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 13 d3 c15 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,2,3,4,5,6,8,9,10,11,12] := remove (a 19) 13 [0,1,2,3,4,5,6,8,9,10,11,12,13] d19 b0
  have b1 : a 14 ≠ 1 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b1
  have b2 : a 14 ≠ 3 := exclude [0,1] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t1 b2
  have b3 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t3 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b3
  have b4 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t3 b4
  have b5 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b5
  have b6 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,3,5,6,7,8,9,10,11] := remove (a 24) 4 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,2,3,6,7,8,9,10,11] := remove (a 24) 5 [0,2,3,5,6,7,8,9,10,11] t6 b7
  have b8 : a 24 ≠ 6 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,2,3,7,8,9,10,11] := remove (a 24) 6 [0,2,3,6,7,8,9,10,11] t7 b8
  have b9 : a 24 ≠ 7 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,2,3,8,9,10,11] := remove (a 24) 7 [0,2,3,7,8,9,10,11] t8 b9
  have b10 : a 24 ≠ 9 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,2,3,8,10,11] := remove (a 24) 9 [0,2,3,8,9,10,11] t9 b10
  have b11 : a 24 ≠ 10 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 10 d8 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,2,3,8,11] := remove (a 24) 10 [0,2,3,8,10,11] t10 b11
  have b12 : a 24 ≠ 11 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,2,3,8] := remove (a 24) 11 [0,2,3,8,11] t11 b12
  have b13 : a 25 ≠ 5 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 5 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d25 b13
  have b14 : a 25 ≠ 7 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 7 [0,1,2,3,4,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 25 ≠ 11 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,2,3,4,6,8,9,10,12,13,14,15,16,17] := remove (a 25) 11 [0,1,2,3,4,6,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t12 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,4,6,8,9,10,12,13,14,15,16,17])
    (d9 : a 9 ∈ [0,2])
    (d11 : a 11 ∈ [0,2,4,6])
    (d10 : a 10 ∈ [0,3])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 25 ∈ [0,1,2,3,4,6,8,9,10,13,15,17] ∧ a 11 ∈ [0,6] ∧ a 26 ∈ [0,1,2,3,7,9,11] ∧ a 27 ∈ [0,1,2,3,10,11,12,13,14,15,16,17] := by
  have b0 : a 25 ≠ 12 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,2,3,4,6,8,9,10,13,14,15,16,17] := remove (a 25) 12 [0,1,2,3,4,6,8,9,10,12,13,14,15,16,17] d25 b0
  have b1 : a 25 ≠ 14 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 14 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,2,3,4,6,8,9,10,13,15,16,17] := remove (a 25) 14 [0,1,2,3,4,6,8,9,10,13,14,15,16,17] t0 b1
  have b2 : a 25 ≠ 16 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,2,3,4,6,8,9,10,13,15,17] := remove (a 25) 16 [0,1,2,3,4,6,8,9,10,13,15,16,17] t1 b2
  have b3 : a 11 ≠ 2 := exclude [0,3] (fun u v => edge r35 v u) (a 11) (a 10) 2 d10 c35 (by decide +kernel)
  have t3 : a 11 ∈ [0,4,6] := remove (a 11) 2 [0,2,4,6] d11 b3
  have b4 : a 11 ≠ 4 := exclude [0,3] (fun u v => edge r35 v u) (a 11) (a 10) 4 d10 c35 (by decide +kernel)
  have t4 : a 11 ∈ [0,6] := remove (a 11) 4 [0,4,6] t3 b4
  have b5 : a 26 ≠ 4 := exclude [0,3] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 26) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b5
  have b6 : a 26 ≠ 5 := exclude [0,3] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 26) 5 [0,1,2,3,5,6,7,8,9,10,11] t5 b6
  have b7 : a 26 ≠ 6 := exclude [0,3] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 26) 6 [0,1,2,3,6,7,8,9,10,11] t6 b7
  have b8 : a 26 ≠ 8 := exclude [0,3] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,2,3,7,9,10,11] := remove (a 26) 8 [0,1,2,3,7,8,9,10,11] t7 b8
  have b9 : a 26 ≠ 10 := exclude [0,3] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0,1,2,3,7,9,11] := remove (a 26) 10 [0,1,2,3,7,9,10,11] t8 b9
  have b10 : a 27 ≠ 4 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 4 t4 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d27 b10
  have b11 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 t4 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 27 ≠ 6 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 6 t4 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 27 ≠ 7 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 7 t4 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 8 t4 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17] := remove (a 27) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 27 ≠ 9 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 9 t4 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,2,3,10,11,12,13,14,15,16,17] := remove (a 27) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t2 (And.intro t4 (And.intro t9 (t15)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_195
