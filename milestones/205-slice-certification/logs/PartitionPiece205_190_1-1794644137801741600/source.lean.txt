import PartitionData205_190
namespace PartitionCover205_190
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,8,9,10,11,13])
    (d9 : a 9 ∈ [0,1])
    (d11 : a 11 ∈ [0,2,6,8])
    (d10 : a 10 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,2,6,7,8])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,5,6,11])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,1])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 25 ∈ [0,1,2,3,8,9,10,11] ∧ a 11 ∈ [0,6] ∧ a 14 ∈ [0,6] ∧ a 26 ∈ [0,1,2,4] ∧ a 15 ∈ [0,6] ∧ a 27 ∈ [0,1] ∧ a 28 ∈ [0,2] := by
  have b0 : a 25 ≠ 13 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,2,3,8,9,10,11] := remove (a 25) 13 [0,1,2,3,8,9,10,11,13] d25 b0
  have b1 : a 11 ≠ 2 := exclude [0,6] (fun u v => edge r35 v u) (a 11) (a 10) 2 d10 c35 (by decide +kernel)
  have t1 : a 11 ∈ [0,6,8] := remove (a 11) 2 [0,2,6,8] d11 b1
  have b2 : a 11 ≠ 8 := exclude [0,6] (fun u v => edge r35 v u) (a 11) (a 10) 8 d10 c35 (by decide +kernel)
  have t2 : a 11 ∈ [0,6] := remove (a 11) 8 [0,6,8] t1 b2
  have b3 : a 14 ≠ 1 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,6,7,8] := remove (a 14) 1 [0,1,2,6,7,8] d14 b3
  have b4 : a 14 ≠ 2 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 2 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,6,7,8] := remove (a 14) 2 [0,2,6,7,8] t3 b4
  have b5 : a 14 ≠ 7 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 7 d10 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,6,8] := remove (a 14) 7 [0,6,7,8] t4 b5
  have b6 : a 14 ≠ 8 := exclude [0,6] (fun u v => edge r36 v u) (a 14) (a 10) 8 d10 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,6] := remove (a 14) 8 [0,6,8] t5 b6
  have b7 : a 26 ≠ 3 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,2,4,5] := remove (a 26) 3 [0,1,2,3,4,5] d26 b7
  have b8 : a 26 ≠ 5 := exclude [0,6] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,2,4] := remove (a 26) 5 [0,1,2,4,5] t7 b8
  have b9 : a 15 ≠ 5 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 5 t2 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0,6,11] := remove (a 15) 5 [0,5,6,11] d15 b9
  have b10 : a 15 ≠ 11 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 11 t2 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0,6] := remove (a 15) 11 [0,6,11] t9 b10
  have b11 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 2 t2 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,3,4,5] := remove (a 27) 2 [0,1,2,3,4,5] d27 b11
  have b12 : a 27 ≠ 3 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 3 t2 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,4,5] := remove (a 27) 3 [0,1,3,4,5] t11 b12
  have b13 : a 27 ≠ 4 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 4 t2 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,5] := remove (a 27) 4 [0,1,4,5] t12 b13
  have b14 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 t2 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1] := remove (a 27) 5 [0,1,5] t13 b14
  have b15 : a 28 ≠ 1 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2] := remove (a 28) 1 [0,1,2] d28 b15
  exact And.intro t0 (And.intro t2 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t14 (t15))))))

theorem chunk5 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,6])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,6])
    (d18 : a 18 ∈ [0,1,2])
    (d16 : a 16 ∈ [0,2])
    (d24 : a 24 ∈ [0,2,4,6])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    : a 28 ∈ [0] ∧ a 29 ∈ [0,1,2,3,8,9,10,11] ∧ a 30 ∈ [0,1,3,5] ∧ a 31 ∈ [0,3] ∧ a 18 ∈ [0] ∧ a 24 ∈ [0,4,6] := by
  have b0 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b0
  have b1 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13] := remove (a 29) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13] d29 b1
  have b2 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,2,3,6,7,8,9,10,11,12,13] := remove (a 29) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13] t1 b2
  have b3 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,2,3,7,8,9,10,11,12,13] := remove (a 29) 6 [0,1,2,3,6,7,8,9,10,11,12,13] t2 b3
  have b4 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,2,3,8,9,10,11,12,13] := remove (a 29) 7 [0,1,2,3,7,8,9,10,11,12,13] t3 b4
  have b5 : a 29 ≠ 12 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,2,3,8,9,10,11,13] := remove (a 29) 12 [0,1,2,3,8,9,10,11,12,13] t4 b5
  have b6 : a 29 ≠ 13 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,2,3,8,9,10,11] := remove (a 29) 13 [0,1,2,3,8,9,10,11,13] t5 b6
  have b7 : a 30 ≠ 2 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,3,4,5] := remove (a 30) 2 [0,1,2,3,4,5] d30 b7
  have b8 : a 30 ≠ 4 := exclude [0,6] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,3,5] := remove (a 30) 4 [0,1,3,4,5] t7 b8
  have b9 : a 31 ≠ 1 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,2,3,4,5] := remove (a 31) 1 [0,1,2,3,4,5] d31 b9
  have b10 : a 31 ≠ 2 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,3,4,5] := remove (a 31) 2 [0,2,3,4,5] t9 b10
  have b11 : a 31 ≠ 4 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,3,5] := remove (a 31) 4 [0,3,4,5] t10 b11
  have b12 : a 31 ≠ 5 := exclude [0,6] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,3] := remove (a 31) 5 [0,3,5] t11 b12
  have b13 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 1 d16 c49 (by decide +kernel)
  have t13 : a 18 ∈ [0,2] := remove (a 18) 1 [0,1,2] d18 b13
  have b14 : a 18 ≠ 2 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 2 d16 c49 (by decide +kernel)
  have t14 : a 18 ∈ [0] := remove (a 18) 2 [0,2] t13 b14
  have b15 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r51 v u) (a 24) (a 16) 2 d16 c51 (by decide +kernel)
  have t15 : a 24 ∈ [0,4,6] := remove (a 24) 2 [0,2,4,6] d24 b15
  exact And.intro t0 (And.intro t6 (And.intro t8 (And.intro t12 (And.intro t14 (t15)))))

theorem chunk6 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,4,6])
    (d16 : a 16 ∈ [0,2])
    (d21 : a 21 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,3,5])
    (d19 : a 19 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,8,9,10,11])
    (d25 : a 25 ∈ [0,1,2,3,8,9,10,11])
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 24 ∈ [0,4] ∧ a 21 ∈ [0,2] ∧ a 23 ∈ [0,1] ∧ a 29 ∈ [0,8] ∧ a 25 ∈ [0,8,9] := by
  have b0 : a 24 ≠ 6 := exclude [0,2] (fun u v => edge r51 v u) (a 24) (a 16) 6 d16 c51 (by decide +kernel)
  have t0 : a 24 ∈ [0,4] := remove (a 24) 6 [0,4,6] d24 b0
  have b1 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t1 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b1
  have b2 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 3 d17 c53 (by decide +kernel)
  have t2 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] t1 b2
  have b3 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,1,5] := remove (a 23) 3 [0,1,3,5] d23 b3
  have b4 : a 23 ≠ 5 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,1] := remove (a 23) 5 [0,1,5] t3 b4
  have b5 : a 29 ≠ 1 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 1 t2 c64 (by decide +kernel)
  have t5 : a 29 ∈ [0,2,3,8,9,10,11] := remove (a 29) 1 [0,1,2,3,8,9,10,11] d29 b5
  have b6 : a 29 ≠ 2 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 2 t2 c64 (by decide +kernel)
  have t6 : a 29 ∈ [0,3,8,9,10,11] := remove (a 29) 2 [0,2,3,8,9,10,11] t5 b6
  have b7 : a 29 ≠ 3 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 3 t2 c64 (by decide +kernel)
  have t7 : a 29 ∈ [0,8,9,10,11] := remove (a 29) 3 [0,3,8,9,10,11] t6 b7
  have b8 : a 29 ≠ 9 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 9 t2 c64 (by decide +kernel)
  have t8 : a 29 ∈ [0,8,10,11] := remove (a 29) 9 [0,8,9,10,11] t7 b8
  have b9 : a 29 ≠ 10 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 10 t2 c64 (by decide +kernel)
  have t9 : a 29 ∈ [0,8,11] := remove (a 29) 10 [0,8,10,11] t8 b9
  have b10 : a 29 ≠ 11 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 11 t2 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0,8] := remove (a 29) 11 [0,8,11] t9 b10
  have b11 : a 25 ≠ 2 := exclude [0,4] (fun u v => edge r68 v u) (a 25) (a 24) 2 t0 c68 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,3,8,9,10,11] := remove (a 25) 2 [0,1,2,3,8,9,10,11] d25 b11
  have b12 : a 25 ≠ 3 := exclude [0,4] (fun u v => edge r68 v u) (a 25) (a 24) 3 t0 c68 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,8,9,10,11] := remove (a 25) 3 [0,1,3,8,9,10,11] t11 b12
  have b13 : a 25 ≠ 10 := exclude [0,4] (fun u v => edge r68 v u) (a 25) (a 24) 10 t0 c68 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,8,9,11] := remove (a 25) 10 [0,1,8,9,10,11] t12 b13
  have b14 : a 25 ≠ 11 := exclude [0,4] (fun u v => edge r68 v u) (a 25) (a 24) 11 t0 c68 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,8,9] := remove (a 25) 11 [0,1,8,9,11] t13 b14
  have b15 : a 25 ≠ 1 := exclude [0,8] (edge r72) (a 25) (a 29) 1 t10 c72 (by decide +kernel)
  have t15 : a 25 ∈ [0,8,9] := remove (a 25) 1 [0,1,8,9] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t10 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,8,9])
    (d29 : a 29 ∈ [0,8])
    (d26 : a 26 ∈ [0,1,2,4])
    (d27 : a 27 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,3,5])
    (d2 : a 2 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,2])
    (d7 : a 7 ∈ [0,1,3,5])
    (d15 : a 15 ∈ [0,6])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 25 ∈ [0,8] ∧ a 26 ∈ [0,1] ∧ a 30 ∈ [0,1] ∧ a 2 ∈ [0,2] ∧ a 7 ∈ [0,1] := by
  have b0 : a 25 ≠ 9 := exclude [0,8] (edge r72) (a 25) (a 29) 9 d29 c72 (by decide +kernel)
  have t0 : a 25 ∈ [0,8] := remove (a 25) 9 [0,8,9] d25 b0
  have b1 : a 26 ≠ 2 := exclude [0,1] (edge r73) (a 26) (a 27) 2 d27 c73 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,4] := remove (a 26) 2 [0,1,2,4] d26 b1
  have b2 : a 26 ≠ 4 := exclude [0,1] (edge r73) (a 26) (a 27) 4 d27 c73 (by decide +kernel)
  have t2 : a 26 ∈ [0,1] := remove (a 26) 4 [0,1,4] t1 b2
  have b3 : a 30 ≠ 3 := exclude [0,1] (fun u v => edge r74 v u) (a 30) (a 26) 3 t2 c74 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,5] := remove (a 30) 3 [0,1,3,5] d30 b3
  have b4 : a 30 ≠ 5 := exclude [0,1] (fun u v => edge r74 v u) (a 30) (a 26) 5 t2 c74 (by decide +kernel)
  have t4 : a 30 ∈ [0,1] := remove (a 30) 5 [0,1,5] t3 b4
  have b5 : a 2 ≠ 1 := exclude [0,2] (edge r10) (a 2) (a 6) 1 d6 c10 (by decide +kernel)
  have t5 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b5
  have b6 : a 2 ≠ 3 := exclude [0,2] (edge r10) (a 2) (a 6) 3 d6 c10 (by decide +kernel)
  have t6 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t5 b6
  have b7 : a 7 ≠ 3 := exclude [0,6] (edge r26) (a 7) (a 15) 3 d15 c26 (by decide +kernel)
  have t7 : a 7 ∈ [0,1,5] := remove (a 7) 3 [0,1,3,5] d7 b7
  have b8 : a 7 ≠ 5 := exclude [0,6] (edge r26) (a 7) (a 15) 5 d15 c26 (by decide +kernel)
  have t8 : a 7 ∈ [0,1] := remove (a 7) 5 [0,1,5] t7 b8
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (t8))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_190
