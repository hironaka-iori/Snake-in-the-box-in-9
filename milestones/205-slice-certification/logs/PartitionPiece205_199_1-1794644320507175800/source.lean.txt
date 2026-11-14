import PartitionData205_199
namespace PartitionCover205_199
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,2,3,4,5])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d9 : a 9 ∈ [0,4])
    (d11 : a 11 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 22 ∈ [0,4] ∧ a 15 ∈ [0,1,2,4] ∧ a 25 ∈ [0,1,6,7] ∧ a 11 ∈ [0,1] ∧ a 26 ∈ [0,4,6,7] := by
  have b0 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0,3,4,5] := remove (a 22) 2 [0,2,3,4,5] d22 b0
  have b1 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,4,5] := remove (a 22) 3 [0,3,4,5] t0 b1
  have b2 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,4] := remove (a 22) 5 [0,4,5] t1 b2
  have b3 : a 15 ≠ 3 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,4,5] := remove (a 15) 3 [0,1,2,3,4,5] d15 b3
  have b4 : a 15 ≠ 5 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,2,4] := remove (a 15) 5 [0,1,2,4,5] t3 b4
  have b5 : a 25 ≠ 2 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 25) 2 [0,1,2,3,4,5,6,7,8,9] d25 b5
  have b6 : a 25 ≠ 3 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,4,5,6,7,8,9] := remove (a 25) 3 [0,1,3,4,5,6,7,8,9] t5 b6
  have b7 : a 25 ≠ 4 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,5,6,7,8,9] := remove (a 25) 4 [0,1,4,5,6,7,8,9] t6 b7
  have b8 : a 25 ≠ 5 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,6,7,8,9] := remove (a 25) 5 [0,1,5,6,7,8,9] t7 b8
  have b9 : a 25 ≠ 8 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,6,7,9] := remove (a 25) 8 [0,1,6,7,8,9] t8 b9
  have b10 : a 25 ≠ 9 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,6,7] := remove (a 25) 9 [0,1,6,7,9] t9 b10
  have b11 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r35 v u) (a 11) (a 10) 2 d10 c35 (by decide +kernel)
  have t11 : a 11 ∈ [0,1] := remove (a 11) 2 [0,1,2] d11 b11
  have b12 : a 26 ≠ 1 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3,4,5,6,7] := remove (a 26) 1 [0,1,2,3,4,5,6,7] d26 b12
  have b13 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,3,4,5,6,7] := remove (a 26) 2 [0,2,3,4,5,6,7] t12 b13
  have b14 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,4,5,6,7] := remove (a 26) 3 [0,3,4,5,6,7] t13 b14
  have b15 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,4,6,7] := remove (a 26) 5 [0,4,5,6,7] t14 b15
  exact And.intro t2 (And.intro t4 (And.intro t10 (And.intro t11 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,4,6,7])
    (d10 : a 10 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2,4])
    (d11 : a 11 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7])
    (d12 : a 12 ∈ [0,2])
    (d29 : a 29 ∈ [0,1,2])
    (d13 : a 13 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,5,6,11])
    (d16 : a 16 ∈ [0,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    : a 26 ∈ [0,4] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,2,3,4] ∧ a 28 ∈ [0,1,4,5] ∧ a 29 ∈ [0,1] ∧ a 31 ∈ [0,2] ∧ a 17 ∈ [0,6] ∧ a 24 ∈ [0,3,4,5] := by
  have b0 : a 26 ≠ 6 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,4,7] := remove (a 26) 6 [0,4,6,7] d26 b0
  have b1 : a 26 ≠ 7 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,4] := remove (a 26) 7 [0,4,7] t0 b1
  have b2 : a 15 ≠ 2 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,4] := remove (a 15) 2 [0,1,2,4] d15 b2
  have b3 : a 15 ≠ 4 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,1] := remove (a 15) 4 [0,1,4] t2 b3
  have b4 : a 27 ≠ 1 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b4
  have b5 : a 27 ≠ 5 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,2,3,4] := remove (a 27) 5 [0,2,3,4,5] t4 b5
  have b6 : a 28 ≠ 2 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,3,4,5,6,7] := remove (a 28) 2 [0,1,2,3,4,5,6,7] d28 b6
  have b7 : a 28 ≠ 3 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,4,5,6,7] := remove (a 28) 3 [0,1,3,4,5,6,7] t6 b7
  have b8 : a 28 ≠ 6 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,4,5,7] := remove (a 28) 6 [0,1,4,5,6,7] t7 b8
  have b9 : a 28 ≠ 7 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,4,5] := remove (a 28) 7 [0,1,4,5,7] t8 b9
  have b10 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1] := remove (a 29) 2 [0,1,2] d29 b10
  have b11 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 1 t3 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,2] := remove (a 31) 1 [0,1,2] d31 b11
  have b12 : a 17 ≠ 5 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 5 d16 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,6,11] := remove (a 17) 5 [0,5,6,11] d17 b12
  have b13 : a 17 ≠ 11 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 11 d16 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0,6] := remove (a 17) 11 [0,6,11] t12 b13
  have b14 : a 24 ≠ 1 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 1 d16 c51 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,3,4,5] := remove (a 24) 1 [0,1,2,3,4,5] d24 b14
  have b15 : a 24 ≠ 2 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 2 d16 c51 (by decide +kernel)
  have t15 : a 24 ∈ [0,3,4,5] := remove (a 24) 2 [0,2,3,4,5] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (t15)))))))

theorem chunk6 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,3,4,5])
    (d16 : a 16 ∈ [0,3])
    (d25 : a 25 ∈ [0,1,6,7])
    (d17 : a 17 ∈ [0,6])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d18 : a 18 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d27 : a 27 ∈ [0,2,3,4])
    (d20 : a 20 ∈ [0,1])
    (d21 : a 21 ∈ [0,3])
    (d28 : a 28 ∈ [0,1,4,5])
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    : a 24 ∈ [0,3] ∧ a 25 ∈ [0,6] ∧ a 19 ∈ [0,4] ∧ a 23 ∈ [0,4] ∧ a 27 ∈ [0,4] ∧ a 20 ∈ [0] ∧ a 28 ∈ [0,4,5] := by
  have b0 : a 24 ≠ 4 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 4 d16 c51 (by decide +kernel)
  have t0 : a 24 ∈ [0,3,5] := remove (a 24) 4 [0,3,4,5] d24 b0
  have b1 : a 24 ≠ 5 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 5 d16 c51 (by decide +kernel)
  have t1 : a 24 ∈ [0,3] := remove (a 24) 5 [0,3,5] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 1 d17 c54 (by decide +kernel)
  have t2 : a 25 ∈ [0,6,7] := remove (a 25) 1 [0,1,6,7] d25 b2
  have b3 : a 25 ≠ 7 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 7 d17 c54 (by decide +kernel)
  have t3 : a 25 ∈ [0,6] := remove (a 25) 7 [0,6,7] t2 b3
  have b4 : a 19 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t4 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b4
  have b5 : a 19 ≠ 2 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t5 : a 19 ∈ [0,3,4,5] := remove (a 19) 2 [0,2,3,4,5] t4 b5
  have b6 : a 19 ≠ 3 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t6 : a 19 ∈ [0,4,5] := remove (a 19) 3 [0,3,4,5] t5 b6
  have b7 : a 19 ≠ 5 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0,4] := remove (a 19) 5 [0,4,5] t6 b7
  have b8 : a 23 ≠ 1 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 1 t7 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,2,3,4,5] := remove (a 23) 1 [0,1,2,3,4,5] d23 b8
  have b9 : a 23 ≠ 2 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 2 t7 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,3,4,5] := remove (a 23) 2 [0,2,3,4,5] t8 b9
  have b10 : a 23 ≠ 3 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 3 t7 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,4,5] := remove (a 23) 3 [0,3,4,5] t9 b10
  have b11 : a 23 ≠ 5 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 5 t7 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,4] := remove (a 23) 5 [0,4,5] t10 b11
  have b12 : a 27 ≠ 2 := exclude [0,4] (fun u v => edge r59 v u) (a 27) (a 19) 2 t7 c59 (by decide +kernel)
  have t12 : a 27 ∈ [0,3,4] := remove (a 27) 2 [0,2,3,4] d27 b12
  have b13 : a 27 ≠ 3 := exclude [0,4] (fun u v => edge r59 v u) (a 27) (a 19) 3 t7 c59 (by decide +kernel)
  have t13 : a 27 ∈ [0,4] := remove (a 27) 3 [0,3,4] t12 b13
  have b14 : a 20 ≠ 1 := exclude [0,3] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t14 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b14
  have b15 : a 28 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 1 t14 c62 (by decide +kernel)
  have t15 : a 28 ∈ [0,4,5] := remove (a 28) 1 [0,1,4,5] d28 b15
  exact And.intro t1 (And.intro t3 (And.intro t7 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))))

theorem chunk7 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,4,5])
    (d20 : a 20 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (d22 : a 22 ∈ [0,4])
    (d26 : a 26 ∈ [0,4])
    (c62 : edge r62 (a 20) (a 28)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 28 ∈ [0,4] ∧ a 30 ∈ [0,4] := by
  have b0 : a 28 ≠ 5 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 5 d20 c62 (by decide +kernel)
  have t0 : a 28 ∈ [0,4] := remove (a 28) 5 [0,4,5] d28 b0
  have b1 : a 30 ≠ 2 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 2 d22 c66 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,3,4,5,6,7] := remove (a 30) 2 [0,1,2,3,4,5,6,7] d30 b1
  have b2 : a 30 ≠ 3 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 3 d22 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,4,5,6,7] := remove (a 30) 3 [0,1,3,4,5,6,7] t1 b2
  have b3 : a 30 ≠ 6 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 6 d22 c66 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,4,5,7] := remove (a 30) 6 [0,1,4,5,6,7] t2 b3
  have b4 : a 30 ≠ 7 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 7 d22 c66 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,4,5] := remove (a 30) 7 [0,1,4,5,7] t3 b4
  have b5 : a 30 ≠ 1 := exclude [0,4] (fun u v => edge r74 v u) (a 30) (a 26) 1 d26 c74 (by decide +kernel)
  have t5 : a 30 ∈ [0,4,5] := remove (a 30) 1 [0,1,4,5] t4 b5
  have b6 : a 30 ≠ 5 := exclude [0,4] (fun u v => edge r74 v u) (a 30) (a 26) 5 d26 c74 (by decide +kernel)
  have t6 : a 30 ∈ [0,4] := remove (a 30) 5 [0,4,5] t5 b6
  exact And.intro t0 (t6)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_199
