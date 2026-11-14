import PartitionData205_170
namespace PartitionCover205_170
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,3,5,6,7,8,9,10,11])
    (d8 : a 8 ∈ [0])
    (d11 : a 11 ∈ [0,8,10,11])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 24 ∈ [0,3,10] ∧ a 11 ∈ [0] ∧ a 25 ∈ [0,1,9] := by
  have b0 : a 24 ≠ 5 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,3,6,7,8,9,10,11] := remove (a 24) 5 [0,3,5,6,7,8,9,10,11] d24 b0
  have b1 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,3,7,8,9,10,11] := remove (a 24) 6 [0,3,6,7,8,9,10,11] t0 b1
  have b2 : a 24 ≠ 7 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 7 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,3,8,9,10,11] := remove (a 24) 7 [0,3,7,8,9,10,11] t1 b2
  have b3 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,3,9,10,11] := remove (a 24) 8 [0,3,8,9,10,11] t2 b3
  have b4 : a 24 ≠ 9 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 9 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,3,10,11] := remove (a 24) 9 [0,3,9,10,11] t3 b4
  have b5 : a 24 ≠ 11 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 11 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0,3,10] := remove (a 24) 11 [0,3,10,11] t4 b5
  have b6 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 8 d9 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0,10,11] := remove (a 11) 8 [0,8,10,11] d11 b6
  have b7 : a 11 ≠ 10 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 10 d9 c32 (by decide +kernel)
  have t7 : a 11 ∈ [0,11] := remove (a 11) 10 [0,10,11] t6 b7
  have b8 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 11 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0] := remove (a 11) 11 [0,11] t7 b8
  have b9 : a 25 ≠ 2 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9] d25 b9
  have b10 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,4,5,6,7,8,9] := remove (a 25) 3 [0,1,3,4,5,6,7,8,9] t9 b10
  have b11 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,5,6,7,8,9] := remove (a 25) 4 [0,1,4,5,6,7,8,9] t10 b11
  have b12 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,6,7,8,9] := remove (a 25) 5 [0,1,5,6,7,8,9] t11 b12
  have b13 : a 25 ≠ 6 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,7,8,9] := remove (a 25) 6 [0,1,6,7,8,9] t12 b13
  have b14 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,8,9] := remove (a 25) 7 [0,1,7,8,9] t13 b14
  have b15 : a 25 ≠ 8 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,9] := remove (a 25) 8 [0,1,8,9] t14 b15
  exact And.intro t5 (And.intro t8 (t15))

theorem chunk13 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,9])
    (d9 : a 9 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,19])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 25 ∈ [0,1] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0,2,4,6,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 25 ≠ 9 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1] := remove (a 25) 9 [0,1,9] d25 b0
  have b1 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b1
  have b2 : a 14 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 2 d10 c36 (by decide +kernel)
  have t2 : a 14 ∈ [0,3] := remove (a 14) 2 [0,2,3] t1 b2
  have b3 : a 14 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0] := remove (a 14) 3 [0,3] t2 b3
  have b4 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,2,3,4,5] := remove (a 26) 1 [0,1,2,3,4,5] d26 b4
  have b5 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,3,4,5] := remove (a 26) 2 [0,2,3,4,5] t4 b5
  have b6 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,4,5] := remove (a 26) 3 [0,3,4,5] t5 b6
  have b7 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,5] := remove (a 26) 4 [0,4,5] t6 b7
  have b8 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 5 [0,5] t7 b8
  have b9 : a 15 ≠ 19 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 19 d11 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 19 [0,19] d15 b9
  have b10 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d27 b10
  have b11 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 5 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 7 [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,2,4,6,9,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 8 [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,2,4,6,10,11,12,13,14,15,16,17,18,19] := remove (a 27) 9 [0,2,4,6,9,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t0 (And.intro t3 (And.intro t8 (And.intro t9 (t15))))

theorem chunk14 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2,4,6,10,11,12,13,14,15,16,17,18,19])
    (d11 : a 11 ∈ [0])
    (d13 : a 13 ∈ [0,2,3])
    (d12 : a 12 ∈ [0,5])
    (d14 : a 14 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 27 ∈ [0,2,4,6] ∧ a 13 ∈ [0,2] ∧ a 12 ∈ [0] ∧ a 28 ∈ [0,5,6,7,8,9] := by
  have b0 : a 27 ≠ 10 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,2,4,6,11,12,13,14,15,16,17,18,19] := remove (a 27) 10 [0,2,4,6,10,11,12,13,14,15,16,17,18,19] d27 b0
  have b1 : a 27 ≠ 11 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,4,6,12,13,14,15,16,17,18,19] := remove (a 27) 11 [0,2,4,6,11,12,13,14,15,16,17,18,19] t0 b1
  have b2 : a 27 ≠ 12 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 12 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,2,4,6,13,14,15,16,17,18,19] := remove (a 27) 12 [0,2,4,6,12,13,14,15,16,17,18,19] t1 b2
  have b3 : a 27 ≠ 13 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 13 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,2,4,6,14,15,16,17,18,19] := remove (a 27) 13 [0,2,4,6,13,14,15,16,17,18,19] t2 b3
  have b4 : a 27 ≠ 14 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 14 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,2,4,6,15,16,17,18,19] := remove (a 27) 14 [0,2,4,6,14,15,16,17,18,19] t3 b4
  have b5 : a 27 ≠ 15 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 15 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,2,4,6,16,17,18,19] := remove (a 27) 15 [0,2,4,6,15,16,17,18,19] t4 b5
  have b6 : a 27 ≠ 16 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 16 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,2,4,6,17,18,19] := remove (a 27) 16 [0,2,4,6,16,17,18,19] t5 b6
  have b7 : a 27 ≠ 17 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 17 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,2,4,6,18,19] := remove (a 27) 17 [0,2,4,6,17,18,19] t6 b7
  have b8 : a 27 ≠ 18 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 18 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,2,4,6,19] := remove (a 27) 18 [0,2,4,6,18,19] t7 b8
  have b9 : a 27 ≠ 19 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 19 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,2,4,6] := remove (a 27) 19 [0,2,4,6,19] t8 b9
  have b10 : a 13 ≠ 3 := exclude [0,5] (fun u v => edge r40 v u) (a 13) (a 12) 3 d12 c40 (by decide +kernel)
  have t10 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] d13 b10
  have b11 : a 12 ≠ 5 := exclude [0] (edge r41) (a 12) (a 14) 5 d14 c41 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 5 [0,5] d12 b11
  have b12 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t11 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9] d28 b12
  have b13 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 t11 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,3,4,5,6,7,8,9] := remove (a 28) 2 [0,2,3,4,5,6,7,8,9] t12 b13
  have b14 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 t11 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,4,5,6,7,8,9] := remove (a 28) 3 [0,3,4,5,6,7,8,9] t13 b14
  have b15 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 t11 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,5,6,7,8,9] := remove (a 28) 4 [0,4,5,6,7,8,9] t14 b15
  exact And.intro t9 (And.intro t10 (And.intro t11 (t15)))

theorem chunk15 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,5,6,7,8,9])
    (d12 : a 12 ∈ [0])
    (d13 : a 13 ∈ [0,2])
    (d15 : a 15 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d14 : a 14 ∈ [0])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 28 ∈ [0] ∧ a 13 ∈ [0] ∧ a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,18] ∧ a 30 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19] := by
  have b0 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,6,7,8,9] := remove (a 28) 5 [0,5,6,7,8,9] d28 b0
  have b1 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,7,8,9] := remove (a 28) 6 [0,6,7,8,9] t0 b1
  have b2 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,8,9] := remove (a 28) 7 [0,7,8,9] t1 b2
  have b3 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,9] := remove (a 28) 8 [0,8,9] t2 b3
  have b4 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0] := remove (a 28) 9 [0,9] t3 b4
  have b5 : a 13 ≠ 2 := exclude [0] (edge r43) (a 13) (a 15) 2 d15 c43 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b5
  have b6 : a 29 ≠ 13 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 13 t5 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18,19] := remove (a 29) 13 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d29 b6
  have b7 : a 29 ≠ 15 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 15 t5 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,17,18,19] := remove (a 29) 15 [0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18,19] t6 b7
  have b8 : a 29 ≠ 17 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 17 t5 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,18,19] := remove (a 29) 17 [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,17,18,19] t7 b8
  have b9 : a 29 ≠ 19 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 19 t5 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,18] := remove (a 29) 19 [0,1,2,3,4,5,6,7,8,9,10,11,12,14,16,18,19] t8 b9
  have b10 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d30 b10
  have b11 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t4 (And.intro t5 (And.intro t9 (t15)))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_170
