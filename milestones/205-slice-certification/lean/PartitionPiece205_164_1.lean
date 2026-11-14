import PartitionData205_164
namespace PartitionCover205_164
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1,5])
    (d8 : a 8 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,1,3,4,5,7,8,9,11,12,14,16])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 9 ∈ [0,1] ∧ a 24 ∈ [0,1,2] ∧ a 11 ∈ [0,1,4,5] ∧ a 25 ∈ [0,2] := by
  have b0 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t0 : a 9 ∈ [0,1] := remove (a 9) 5 [0,1,5] d9 b0
  have b1 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 3 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,1,2,4,5] := remove (a 24) 3 [0,1,2,3,4,5] d24 b1
  have b2 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,2,5] := remove (a 24) 4 [0,1,2,4,5] t1 b2
  have b3 : a 24 ≠ 5 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,2] := remove (a 24) 5 [0,1,2,5] t2 b3
  have b4 : a 11 ≠ 8 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 8 t0 c32 (by decide +kernel)
  have t4 : a 11 ∈ [0,1,3,4,5,7,9,11,12,14,16] := remove (a 11) 8 [0,1,3,4,5,7,8,9,11,12,14,16] d11 b4
  have b5 : a 11 ≠ 9 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 9 t0 c32 (by decide +kernel)
  have t5 : a 11 ∈ [0,1,3,4,5,7,11,12,14,16] := remove (a 11) 9 [0,1,3,4,5,7,9,11,12,14,16] t4 b5
  have b6 : a 11 ≠ 11 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 11 t0 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0,1,3,4,5,7,12,14,16] := remove (a 11) 11 [0,1,3,4,5,7,11,12,14,16] t5 b6
  have b7 : a 11 ≠ 12 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 12 t0 c32 (by decide +kernel)
  have t7 : a 11 ∈ [0,1,3,4,5,7,14,16] := remove (a 11) 12 [0,1,3,4,5,7,12,14,16] t6 b7
  have b8 : a 11 ≠ 14 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 14 t0 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,3,4,5,7,16] := remove (a 11) 14 [0,1,3,4,5,7,14,16] t7 b8
  have b9 : a 11 ≠ 16 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 16 t0 c32 (by decide +kernel)
  have t9 : a 11 ∈ [0,1,3,4,5,7] := remove (a 11) 16 [0,1,3,4,5,7,16] t8 b9
  have b10 : a 25 ≠ 1 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 1 t0 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,2,3,4,5] := remove (a 25) 1 [0,1,2,3,4,5] d25 b10
  have b11 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 3 t0 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,4,5] := remove (a 25) 3 [0,2,3,4,5] t10 b11
  have b12 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 4 t0 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,2,5] := remove (a 25) 4 [0,2,4,5] t11 b12
  have b13 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 5 t0 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,2] := remove (a 25) 5 [0,2,5] t12 b13
  have b14 : a 11 ≠ 3 := exclude [0,1,2,3,4,5] (edge r39) (a 11) (a 27) 3 d27 c39 (by decide +kernel)
  have t14 : a 11 ∈ [0,1,4,5,7] := remove (a 11) 3 [0,1,3,4,5,7] t9 b14
  have b15 : a 11 ≠ 7 := exclude [0,1,2,3,4,5] (edge r39) (a 11) (a 27) 7 d27 c39 (by decide +kernel)
  have t15 : a 11 ∈ [0,1,4,5] := remove (a 11) 7 [0,1,4,5,7] t14 b15
  exact And.intro t0 (And.intro t3 (And.intro t15 (t13)))

theorem chunk5 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,1,4,5])
    (d13 : a 13 ∈ [0,1,2])
    (d12 : a 12 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d15 : a 15 ∈ [0,1,2])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    : a 27 ∈ [0,2] ∧ a 13 ∈ [0] ∧ a 28 ∈ [0,1] ∧ a 15 ∈ [0] := by
  have b0 : a 27 ≠ 1 := exclude [0,1,4,5] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b0
  have b1 : a 27 ≠ 3 := exclude [0,1,4,5] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,4,5] := remove (a 27) 3 [0,2,3,4,5] t0 b1
  have b2 : a 27 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,2,5] := remove (a 27) 4 [0,2,4,5] t1 b2
  have b3 : a 27 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,2] := remove (a 27) 5 [0,2,5] t2 b3
  have b4 : a 13 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 1 d12 c40 (by decide +kernel)
  have t4 : a 13 ∈ [0,2] := remove (a 13) 1 [0,1,2] d13 b4
  have b5 : a 13 ≠ 2 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 2 d12 c40 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 2 [0,2] t4 b5
  have b6 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 28) 2 [0,1,2,3,4,5,6,7,8,9] d28 b6
  have b7 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,4,5,6,7,8,9] := remove (a 28) 3 [0,1,3,4,5,6,7,8,9] t6 b7
  have b8 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,5,6,7,8,9] := remove (a 28) 4 [0,1,4,5,6,7,8,9] t7 b8
  have b9 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,6,7,8,9] := remove (a 28) 5 [0,1,5,6,7,8,9] t8 b9
  have b10 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,7,8,9] := remove (a 28) 6 [0,1,6,7,8,9] t9 b10
  have b11 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,1,8,9] := remove (a 28) 7 [0,1,7,8,9] t10 b11
  have b12 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,1,9] := remove (a 28) 8 [0,1,8,9] t11 b12
  have b13 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,1] := remove (a 28) 9 [0,1,9] t12 b13
  have b14 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 t5 c43 (by decide +kernel)
  have t14 : a 15 ∈ [0,2] := remove (a 15) 1 [0,1,2] d15 b14
  have b15 : a 15 ≠ 2 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 2 t5 c43 (by decide +kernel)
  have t15 : a 15 ∈ [0] := remove (a 15) 2 [0,2] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t13 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0,2])
    (d27 : a 27 ∈ [0,2])
    (d20 : a 20 ∈ [0,1,2,4,5,6,8,10])
    (d21 : a 21 ∈ [0])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 30 ∈ [0,1,4] ∧ a 31 ∈ [0,1,3,4,5,7,9,11] ∧ a 16 ∈ [0,2] ∧ a 26 ∈ [0,2] ∧ a 23 ∈ [0,1,2,3] ∧ a 27 ∈ [0] ∧ a 20 ∈ [0,1,5,6,8,10] := by
  have b0 : a 30 ≠ 2 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,3,4,5] := remove (a 30) 2 [0,1,2,3,4,5] d30 b0
  have b1 : a 30 ≠ 3 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,4,5] := remove (a 30) 3 [0,1,3,4,5] t0 b1
  have b2 : a 30 ≠ 5 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,4] := remove (a 30) 5 [0,1,4,5] t1 b2
  have b3 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b3
  have b4 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,3,4,5,7,8,9,10,11] := remove (a 31) 6 [0,1,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 31 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,3,4,5,7,9,10,11] := remove (a 31) 8 [0,1,3,4,5,7,8,9,10,11] t4 b5
  have b6 : a 31 ≠ 10 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,3,4,5,7,9,11] := remove (a 31) 10 [0,1,3,4,5,7,9,10,11] t5 b6
  have b7 : a 16 ≠ 1 := exclude [0,2] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t7 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b7
  have b8 : a 16 ≠ 3 := exclude [0,2] (edge r49) (a 16) (a 18) 3 d18 c49 (by decide +kernel)
  have t8 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t7 b8
  have b9 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 1 d18 c57 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b9
  have b10 : a 26 ≠ 3 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 3 d18 c57 (by decide +kernel)
  have t10 : a 26 ∈ [0,2] := remove (a 26) 3 [0,2,3] t9 b10
  have b11 : a 23 ≠ 4 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,2,3,5] := remove (a 23) 4 [0,1,2,3,4,5] d23 b11
  have b12 : a 23 ≠ 5 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,2,3] := remove (a 23) 5 [0,1,2,3,5] t11 b12
  have b13 : a 27 ≠ 2 := exclude [0,2] (fun u v => edge r59 v u) (a 27) (a 19) 2 d19 c59 (by decide +kernel)
  have t13 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b13
  have b14 : a 20 ≠ 2 := exclude [0] (edge r60) (a 20) (a 21) 2 d21 c60 (by decide +kernel)
  have t14 : a 20 ∈ [0,1,4,5,6,8,10] := remove (a 20) 2 [0,1,2,4,5,6,8,10] d20 b14
  have b15 : a 20 ≠ 4 := exclude [0] (edge r60) (a 20) (a 21) 4 d21 c60 (by decide +kernel)
  have t15 : a 20 ∈ [0,1,5,6,8,10] := remove (a 20) 4 [0,1,4,5,6,8,10] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))))

theorem chunk7 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,5,6,8,10])
    (d21 : a 21 ∈ [0])
    (d22 : a 22 ∈ [0,1,3,4,5,7,9,11])
    (d23 : a 23 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    : a 20 ∈ [0,1] ∧ a 22 ∈ [0,1] ∧ a 23 ∈ [0,2] ∧ a 29 ∈ [0,1,6,7,8,9,10,11] := by
  have b0 : a 20 ≠ 5 := exclude [0] (edge r60) (a 20) (a 21) 5 d21 c60 (by decide +kernel)
  have t0 : a 20 ∈ [0,1,6,8,10] := remove (a 20) 5 [0,1,5,6,8,10] d20 b0
  have b1 : a 20 ≠ 6 := exclude [0] (edge r60) (a 20) (a 21) 6 d21 c60 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,8,10] := remove (a 20) 6 [0,1,6,8,10] t0 b1
  have b2 : a 20 ≠ 8 := exclude [0] (edge r60) (a 20) (a 21) 8 d21 c60 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,10] := remove (a 20) 8 [0,1,8,10] t1 b2
  have b3 : a 20 ≠ 10 := exclude [0] (edge r60) (a 20) (a 21) 10 d21 c60 (by decide +kernel)
  have t3 : a 20 ∈ [0,1] := remove (a 20) 10 [0,1,10] t2 b3
  have b4 : a 22 ≠ 3 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 3 t3 c61 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,4,5,7,9,11] := remove (a 22) 3 [0,1,3,4,5,7,9,11] d22 b4
  have b5 : a 22 ≠ 4 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 4 t3 c61 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,5,7,9,11] := remove (a 22) 4 [0,1,4,5,7,9,11] t4 b5
  have b6 : a 22 ≠ 5 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 5 t3 c61 (by decide +kernel)
  have t6 : a 22 ∈ [0,1,7,9,11] := remove (a 22) 5 [0,1,5,7,9,11] t5 b6
  have b7 : a 22 ≠ 7 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 7 t3 c61 (by decide +kernel)
  have t7 : a 22 ∈ [0,1,9,11] := remove (a 22) 7 [0,1,7,9,11] t6 b7
  have b8 : a 22 ≠ 9 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 9 t3 c61 (by decide +kernel)
  have t8 : a 22 ∈ [0,1,11] := remove (a 22) 9 [0,1,9,11] t7 b8
  have b9 : a 22 ≠ 11 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 11 t3 c61 (by decide +kernel)
  have t9 : a 22 ∈ [0,1] := remove (a 22) 11 [0,1,11] t8 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 1 d21 c63 (by decide +kernel)
  have t10 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b10
  have b11 : a 23 ≠ 3 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 3 d21 c63 (by decide +kernel)
  have t11 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t10 b11
  have b12 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 d21 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b12
  have b13 : a 29 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 3 d21 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 29 ≠ 4 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 4 d21 c64 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 29 ≠ 5 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 5 d21 c64 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,6,7,8,9,10,11] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t9 (And.intro t11 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_164
