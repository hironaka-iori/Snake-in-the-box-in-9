import PartitionData205_205
namespace PartitionCover205_205
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,4,5])
    (d9 : a 9 ∈ [0,4])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0,3,5,6])
    (d14 : a 14 ∈ [0,1,3,4])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 13 ∈ [0,4] ∧ a 25 ∈ [0,3] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0,6] ∧ a 14 ∈ [0,3] ∧ a 26 ∈ [0,6,7,8] := by
  have b0 : a 13 ≠ 1 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t0 : a 13 ∈ [0,4,5] := remove (a 13) 1 [0,1,4,5] d13 b0
  have b1 : a 13 ≠ 5 := exclude [0,4] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [0,4] := remove (a 13) 5 [0,4,5] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,3,4,5] := remove (a 25) 1 [0,1,2,3,4,5] d25 b2
  have b3 : a 25 ≠ 2 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,3,4,5] := remove (a 25) 2 [0,2,3,4,5] t2 b3
  have b4 : a 25 ≠ 4 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,3,5] := remove (a 25) 4 [0,3,4,5] t3 b4
  have b5 : a 25 ≠ 5 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,3] := remove (a 25) 5 [0,3,5] t4 b5
  have b6 : a 10 ≠ 2 := exclude [0,3,5,6] (edge r35) (a 10) (a 11) 2 d11 c35 (by decide +kernel)
  have t6 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b6
  have b7 : a 11 ≠ 3 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 3 t6 c35 (by decide +kernel)
  have t7 : a 11 ∈ [0,5,6] := remove (a 11) 3 [0,3,5,6] d11 b7
  have b8 : a 11 ≠ 5 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 5 t6 c35 (by decide +kernel)
  have t8 : a 11 ∈ [0,6] := remove (a 11) 5 [0,5,6] t7 b8
  have b9 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 t6 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,3,4] := remove (a 14) 1 [0,1,3,4] d14 b9
  have b10 : a 14 ≠ 4 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 4 t6 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,3] := remove (a 14) 4 [0,3,4] t9 b10
  have b11 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t6 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,3,4,5,6,7,8] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8] d26 b11
  have b12 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t6 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,3,4,5,6,7,8] := remove (a 26) 2 [0,2,3,4,5,6,7,8] t11 b12
  have b13 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t6 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,4,5,6,7,8] := remove (a 26) 3 [0,3,4,5,6,7,8] t12 b13
  have b14 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t6 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,5,6,7,8] := remove (a 26) 4 [0,4,5,6,7,8] t13 b14
  have b15 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 t6 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,6,7,8] := remove (a 26) 5 [0,5,6,7,8] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t10 (t15)))))

theorem chunk5 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,6,7,8])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1,4,5])
    (d11 : a 11 ∈ [0,6])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,4])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,3])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 26 ∈ [0,7] ∧ a 15 ∈ [0,4] ∧ a 27 ∈ [0,4] ∧ a 29 ∈ [0,3] ∧ a 30 ∈ [0,2,3,4,5,6,7,8] := by
  have b0 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,7,8] := remove (a 26) 6 [0,6,7,8] d26 b0
  have b1 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,7] := remove (a 26) 8 [0,7,8] t0 b1
  have b2 : a 15 ≠ 1 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,4,5] := remove (a 15) 1 [0,1,4,5] d15 b2
  have b3 : a 15 ≠ 5 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,4] := remove (a 15) 5 [0,4,5] t2 b3
  have b4 : a 27 ≠ 1 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,2,3,4,5,6,7,8] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8] d27 b4
  have b5 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,3,4,5,6,7,8] := remove (a 27) 2 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 27 ≠ 3 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,4,5,6,7,8] := remove (a 27) 3 [0,3,4,5,6,7,8] t5 b6
  have b7 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,4,6,7,8] := remove (a 27) 5 [0,4,5,6,7,8] t6 b7
  have b8 : a 27 ≠ 6 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,4,7,8] := remove (a 27) 6 [0,4,6,7,8] t7 b8
  have b9 : a 27 ≠ 7 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,4,8] := remove (a 27) 7 [0,4,7,8] t8 b9
  have b10 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,4] := remove (a 27) 8 [0,4,8] t9 b10
  have b11 : a 29 ≠ 1 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,2,3,4,5] := remove (a 29) 1 [0,1,2,3,4,5] d29 b11
  have b12 : a 29 ≠ 2 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,3,4,5] := remove (a 29) 2 [0,2,3,4,5] t11 b12
  have b13 : a 29 ≠ 4 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,3,5] := remove (a 29) 4 [0,3,4,5] t12 b13
  have b14 : a 29 ≠ 5 := exclude [0,4] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,3] := remove (a 29) 5 [0,3,5] t13 b14
  have b15 : a 30 ≠ 1 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,3,4,5,6,7,8] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8] d30 b15
  exact And.intro t1 (And.intro t3 (And.intro t10 (And.intro t14 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,3])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,4])
    (d20 : a 20 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,2])
    (d19 : a 19 ∈ [0,2,3,4])
    (d17 : a 17 ∈ [0,2])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 30 ∈ [0,3,5,6] ∧ a 31 ∈ [0,1,8,9] ∧ a 20 ∈ [0,2] ∧ a 19 ∈ [0,4] := by
  have b0 : a 30 ≠ 2 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,3,4,5,6,7,8] := remove (a 30) 2 [0,2,3,4,5,6,7,8] d30 b0
  have b1 : a 30 ≠ 4 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,3,5,6,7,8] := remove (a 30) 4 [0,3,4,5,6,7,8] t0 b1
  have b2 : a 30 ≠ 7 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,3,5,6,8] := remove (a 30) 7 [0,3,5,6,7,8] t1 b2
  have b3 : a 30 ≠ 8 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,3,5,6] := remove (a 30) 8 [0,3,5,6,8] t2 b3
  have b4 : a 31 ≠ 2 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b4
  have b5 : a 31 ≠ 3 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 31 ≠ 4 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 31) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 31 ≠ 5 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,6,7,8,9,10,11] := remove (a 31) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 31 ≠ 6 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,7,8,9,10,11] := remove (a 31) 6 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 31 ≠ 7 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,8,9,10,11] := remove (a 31) 7 [0,1,7,8,9,10,11] t8 b9
  have b10 : a 31 ≠ 10 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,8,9,11] := remove (a 31) 10 [0,1,8,9,10,11] t9 b10
  have b11 : a 31 ≠ 11 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,8,9] := remove (a 31) 11 [0,1,8,9,11] t10 b11
  have b12 : a 20 ≠ 1 := exclude [0,2] (fun u v => edge r50 v u) (a 20) (a 16) 1 d16 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b12
  have b13 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r50 v u) (a 20) (a 16) 3 d16 c50 (by decide +kernel)
  have t13 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t12 b13
  have b14 : a 19 ≠ 2 := exclude [0,2] (fun u v => edge r52 v u) (a 19) (a 17) 2 d17 c52 (by decide +kernel)
  have t14 : a 19 ∈ [0,3,4] := remove (a 19) 2 [0,2,3,4] d19 b14
  have b15 : a 19 ≠ 3 := exclude [0,2] (fun u v => edge r52 v u) (a 19) (a 17) 3 d17 c52 (by decide +kernel)
  have t15 : a 19 ∈ [0,4] := remove (a 19) 3 [0,3,4] t14 b15
  exact And.intro t3 (And.intro t11 (And.intro t13 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,4,5])
    (d19 : a 19 ∈ [0,4])
    (d31 : a 31 ∈ [0,1,8,9])
    (d24 : a 24 ∈ [0,2])
    (d25 : a 25 ∈ [0,3])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d30 : a 30 ∈ [0,3,5,6])
    (d26 : a 26 ∈ [0,7])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 23 ∈ [0,4] ∧ a 31 ∈ [0,8] ∧ a 24 ∈ [0] ∧ a 28 ∈ [0] ∧ a 30 ∈ [0,6] := by
  have b0 : a 23 ≠ 1 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,4,5] := remove (a 23) 1 [0,1,4,5] d23 b0
  have b1 : a 23 ≠ 5 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,4] := remove (a 23) 5 [0,4,5] t0 b1
  have b2 : a 31 ≠ 1 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 1 t1 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0,8,9] := remove (a 31) 1 [0,1,8,9] d31 b2
  have b3 : a 31 ≠ 9 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 9 t1 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,8] := remove (a 31) 9 [0,8,9] t2 b3
  have b4 : a 24 ≠ 2 := exclude [0,3] (edge r68) (a 24) (a 25) 2 d25 c68 (by decide +kernel)
  have t4 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b4
  have b5 : a 28 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 1 t4 c70 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9] d28 b5
  have b6 : a 28 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 2 t4 c70 (by decide +kernel)
  have t6 : a 28 ∈ [0,3,4,5,6,7,8,9] := remove (a 28) 2 [0,2,3,4,5,6,7,8,9] t5 b6
  have b7 : a 28 ≠ 3 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 3 t4 c70 (by decide +kernel)
  have t7 : a 28 ∈ [0,4,5,6,7,8,9] := remove (a 28) 3 [0,3,4,5,6,7,8,9] t6 b7
  have b8 : a 28 ≠ 4 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 4 t4 c70 (by decide +kernel)
  have t8 : a 28 ∈ [0,5,6,7,8,9] := remove (a 28) 4 [0,4,5,6,7,8,9] t7 b8
  have b9 : a 28 ≠ 5 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 5 t4 c70 (by decide +kernel)
  have t9 : a 28 ∈ [0,6,7,8,9] := remove (a 28) 5 [0,5,6,7,8,9] t8 b9
  have b10 : a 28 ≠ 6 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 6 t4 c70 (by decide +kernel)
  have t10 : a 28 ∈ [0,7,8,9] := remove (a 28) 6 [0,6,7,8,9] t9 b10
  have b11 : a 28 ≠ 7 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 7 t4 c70 (by decide +kernel)
  have t11 : a 28 ∈ [0,8,9] := remove (a 28) 7 [0,7,8,9] t10 b11
  have b12 : a 28 ≠ 8 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 8 t4 c70 (by decide +kernel)
  have t12 : a 28 ∈ [0,9] := remove (a 28) 8 [0,8,9] t11 b12
  have b13 : a 28 ≠ 9 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 9 t4 c70 (by decide +kernel)
  have t13 : a 28 ∈ [0] := remove (a 28) 9 [0,9] t12 b13
  have b14 : a 30 ≠ 3 := exclude [0,7] (fun u v => edge r74 v u) (a 30) (a 26) 3 d26 c74 (by decide +kernel)
  have t14 : a 30 ∈ [0,5,6] := remove (a 30) 3 [0,3,5,6] d30 b14
  have b15 : a 30 ≠ 5 := exclude [0,7] (fun u v => edge r74 v u) (a 30) (a 26) 5 d26 c74 (by decide +kernel)
  have t15 : a 30 ∈ [0,6] := remove (a 30) 5 [0,5,6] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t13 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_205
