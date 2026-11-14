import PartitionData205_186
namespace PartitionCover205_186
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,12])
    (d11 : a 11 ∈ [0,1,9])
    (d26 : a 26 ∈ [0,1,2])
    (d15 : a 15 ∈ [0,1,5,7])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d13 : a 13 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 26 ∈ [0,2] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0,1,5,6,7] := by
  have b0 : a 10 ≠ 12 := exclude [0,1,9] (edge r35) (a 10) (a 11) 12 d11 c35 (by decide +kernel)
  have t0 : a 10 ∈ [0] := remove (a 10) 12 [0,12] d10 b0
  have b1 : a 11 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 1 t0 c35 (by decide +kernel)
  have t1 : a 11 ∈ [0,9] := remove (a 11) 1 [0,1,9] d11 b1
  have b2 : a 11 ≠ 9 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 9 t0 c35 (by decide +kernel)
  have t2 : a 11 ∈ [0] := remove (a 11) 9 [0,9] t1 b2
  have b3 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t0 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,2] := remove (a 26) 1 [0,1,2] d26 b3
  have b4 : a 15 ≠ 5 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 5 t2 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,7] := remove (a 15) 5 [0,1,5,7] d15 b4
  have b5 : a 15 ≠ 7 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 7 t2 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,1] := remove (a 15) 7 [0,1,7] t4 b5
  have b6 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 t2 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b6
  have b7 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 t2 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,3,4,5] := remove (a 27) 2 [0,2,3,4,5] t6 b7
  have b8 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 t2 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,4,5] := remove (a 27) 3 [0,3,4,5] t7 b8
  have b9 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 t2 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,5] := remove (a 27) 4 [0,4,5] t8 b9
  have b10 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 t2 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0] := remove (a 27) 5 [0,5] t9 b10
  have b11 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b11
  have b12 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 d13 c43 (by decide +kernel)
  have t12 : a 15 ∈ [0] := remove (a 15) 1 [0,1] t5 b12
  have b13 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,3,4,5,6,7] := remove (a 29) 2 [0,1,2,3,4,5,6,7] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,4,5,6,7] := remove (a 29) 3 [0,1,3,4,5,6,7] t13 b14
  have b15 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,5,6,7] := remove (a 29) 4 [0,1,4,5,6,7] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t12 (And.intro t10 (And.intro t11 (t15))))))

theorem chunk13 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,5,6,7])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0])
    (d17 : a 17 ∈ [0,1,3,5,6])
    (d16 : a 16 ∈ [0,2])
    (d20 : a 20 ∈ [0,4,5])
    (d21 : a 21 ∈ [0,1,2,3,4,6,7])
    (d19 : a 19 ∈ [0,1,4,5,11])
    (d18 : a 18 ∈ [0,3,7,20])
    (d22 : a 22 ∈ [0,4])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 29 ∈ [0,1] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0,2] ∧ a 17 ∈ [0,1,6] ∧ a 16 ∈ [0] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0,1,2,3,6,7] ∧ a 19 ∈ [0,1,11] ∧ a 18 ∈ [0,20] := by
  have b0 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,6,7] := remove (a 29) 5 [0,1,5,6,7] d29 b0
  have b1 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,7] := remove (a 29) 6 [0,1,6,7] t0 b1
  have b2 : a 29 ≠ 7 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1] := remove (a 29) 7 [0,1,7] t1 b2
  have b3 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b3
  have b4 : a 31 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,2,3] := remove (a 31) 1 [0,1,2,3] d31 b4
  have b5 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,2] := remove (a 31) 3 [0,2,3] t4 b5
  have b6 : a 17 ≠ 3 := exclude [0,2] (fun u v => edge r48 v u) (a 17) (a 16) 3 d16 c48 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,5,6] := remove (a 17) 3 [0,1,3,5,6] d17 b6
  have b7 : a 17 ≠ 5 := exclude [0,2] (fun u v => edge r48 v u) (a 17) (a 16) 5 d16 c48 (by decide +kernel)
  have t7 : a 17 ∈ [0,1,6] := remove (a 17) 5 [0,1,5,6] t6 b7
  have b8 : a 16 ≠ 2 := exclude [0,4,5] (edge r50) (a 16) (a 20) 2 d20 c50 (by decide +kernel)
  have t8 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b8
  have b9 : a 20 ≠ 4 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 4 t8 c50 (by decide +kernel)
  have t9 : a 20 ∈ [0,5] := remove (a 20) 4 [0,4,5] d20 b9
  have b10 : a 20 ≠ 5 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 5 t8 c50 (by decide +kernel)
  have t10 : a 20 ∈ [0] := remove (a 20) 5 [0,5] t9 b10
  have b11 : a 21 ≠ 4 := exclude [0,1,6] (fun u v => edge r53 v u) (a 21) (a 17) 4 t7 c53 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,2,3,6,7] := remove (a 21) 4 [0,1,2,3,4,6,7] d21 b11
  have b12 : a 19 ≠ 4 := exclude [0,3,7,20] (fun u v => edge r55 v u) (a 19) (a 18) 4 d18 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,5,11] := remove (a 19) 4 [0,1,4,5,11] d19 b12
  have b13 : a 19 ≠ 5 := exclude [0,3,7,20] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,11] := remove (a 19) 5 [0,1,5,11] t12 b13
  have b14 : a 18 ≠ 3 := exclude [0,4] (edge r56) (a 18) (a 22) 3 d22 c56 (by decide +kernel)
  have t14 : a 18 ∈ [0,7,20] := remove (a 18) 3 [0,3,7,20] d18 b14
  have b15 : a 18 ≠ 7 := exclude [0,4] (edge r56) (a 18) (a 22) 7 d22 c56 (by decide +kernel)
  have t15 : a 18 ∈ [0,20] := remove (a 18) 7 [0,7,20] t14 b15
  exact And.intro t2 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t13 (t15))))))))

theorem chunk14 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,20])
    (d22 : a 22 ∈ [0,4])
    (d26 : a 26 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0,1,11])
    (d27 : a 27 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3,6,7])
    (d20 : a 20 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0,2])
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 18 ∈ [0] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0] ∧ a 23 ∈ [0] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0] ∧ a 31 ∈ [0] := by
  have b0 : a 18 ≠ 20 := exclude [0,4] (edge r56) (a 18) (a 22) 20 d22 c56 (by decide +kernel)
  have t0 : a 18 ∈ [0] := remove (a 18) 20 [0,20] d18 b0
  have b1 : a 22 ≠ 4 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 4 t0 c56 (by decide +kernel)
  have t1 : a 22 ∈ [0] := remove (a 22) 4 [0,4] d22 b1
  have b2 : a 26 ≠ 2 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 2 t0 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b2
  have b3 : a 23 ≠ 1 := exclude [0,1,11] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,2,3,4,5] := remove (a 23) 1 [0,1,2,3,4,5] d23 b3
  have b4 : a 23 ≠ 3 := exclude [0,1,11] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,2,4,5] := remove (a 23) 3 [0,2,3,4,5] t3 b4
  have b5 : a 19 ≠ 1 := exclude [0] (edge r59) (a 19) (a 27) 1 d27 c59 (by decide +kernel)
  have t5 : a 19 ∈ [0,11] := remove (a 19) 1 [0,1,11] d19 b5
  have b6 : a 19 ≠ 11 := exclude [0] (edge r59) (a 19) (a 27) 11 d27 c59 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 11 [0,11] t5 b6
  have b7 : a 21 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 1 d20 c60 (by decide +kernel)
  have t7 : a 21 ∈ [0,2,3,6,7] := remove (a 21) 1 [0,1,2,3,6,7] d21 b7
  have b8 : a 21 ≠ 6 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 6 d20 c60 (by decide +kernel)
  have t8 : a 21 ∈ [0,2,3,7] := remove (a 21) 6 [0,2,3,6,7] t7 b8
  have b9 : a 21 ≠ 7 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 7 d20 c60 (by decide +kernel)
  have t9 : a 21 ∈ [0,2,3] := remove (a 21) 7 [0,2,3,7] t8 b9
  have b10 : a 21 ≠ 2 := exclude [0,1] (edge r64) (a 21) (a 29) 2 d29 c64 (by decide +kernel)
  have t10 : a 21 ∈ [0,3] := remove (a 21) 2 [0,2,3] t9 b10
  have b11 : a 21 ≠ 3 := exclude [0,1] (edge r64) (a 21) (a 29) 3 d29 c64 (by decide +kernel)
  have t11 : a 21 ∈ [0] := remove (a 21) 3 [0,3] t10 b11
  have b12 : a 23 ≠ 2 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 2 t1 c65 (by decide +kernel)
  have t12 : a 23 ∈ [0,4,5] := remove (a 23) 2 [0,2,4,5] t4 b12
  have b13 : a 23 ≠ 4 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 4 t1 c65 (by decide +kernel)
  have t13 : a 23 ∈ [0,5] := remove (a 23) 4 [0,4,5] t12 b13
  have b14 : a 23 ≠ 5 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 5 t1 c65 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 5 [0,5] t13 b14
  have b15 : a 31 ≠ 2 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 2 t14 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0] := remove (a 31) 2 [0,2] d31 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t14 (And.intro t6 (And.intro t11 (t15))))))

theorem chunk15 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,3])
    (d29 : a 29 ∈ [0,1])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0,5,13])
    (d17 : a 17 ∈ [0,1,6])
    (d2 : a 2 ∈ [0,11])
    (d7 : a 7 ∈ [0,6])
    (d5 : a 5 ∈ [0,4])
    (d4 : a 4 ∈ [0])
    (d9 : a 9 ∈ [0,3])
    (d11 : a 11 ∈ [0])
    (d19 : a 19 ∈ [0])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 29 ∈ [0] ∧ a 1 ∈ [0] ∧ a 3 ∈ [0] ∧ a 17 ∈ [0] ∧ a 2 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] := by
  have b0 : a 24 ≠ 1 := exclude [0,3] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b0
  have b1 : a 24 ≠ 2 := exclude [0,3] (edge r68) (a 24) (a 25) 2 d25 c68 (by decide +kernel)
  have t1 : a 24 ∈ [0,3] := remove (a 24) 2 [0,2,3] t0 b1
  have b2 : a 24 ≠ 3 := exclude [0,3] (edge r68) (a 24) (a 25) 3 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 3 [0,3] t1 b2
  have b3 : a 25 ≠ 3 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 3 t2 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0] := remove (a 25) 3 [0,3] d25 b3
  have b4 : a 29 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 1 t3 c72 (by decide +kernel)
  have t4 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b4
  have b5 : a 1 ≠ 1 := exclude [0,5,13] (edge r5) (a 1) (a 3) 1 d3 c5 (by decide +kernel)
  have t5 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b5
  have b6 : a 3 ≠ 13 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 13 t5 c5 (by decide +kernel)
  have t6 : a 3 ∈ [0,5] := remove (a 3) 13 [0,5,13] d3 b6
  have b7 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 t5 c8 (by decide +kernel)
  have t7 : a 17 ∈ [0,6] := remove (a 17) 1 [0,1,6] d17 b7
  have b8 : a 2 ≠ 11 := exclude [0,5] (edge r9) (a 2) (a 3) 11 t6 c9 (by decide +kernel)
  have t8 : a 2 ∈ [0] := remove (a 2) 11 [0,11] d2 b8
  have b9 : a 3 ≠ 5 := exclude [0,6] (edge r13) (a 3) (a 7) 5 d7 c13 (by decide +kernel)
  have t9 : a 3 ∈ [0] := remove (a 3) 5 [0,5] t6 b9
  have b10 : a 7 ≠ 6 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 6 t9 c13 (by decide +kernel)
  have t10 : a 7 ∈ [0] := remove (a 7) 6 [0,6] d7 b10
  have b11 : a 5 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t11 : a 5 ∈ [0] := remove (a 5) 4 [0,4] d5 b11
  have b12 : a 9 ≠ 3 := exclude [0] (edge r32) (a 9) (a 11) 3 d11 c32 (by decide +kernel)
  have t12 : a 9 ∈ [0] := remove (a 9) 3 [0,3] d9 b12
  have b13 : a 17 ≠ 6 := exclude [0] (edge r52) (a 17) (a 19) 6 d19 c52 (by decide +kernel)
  have t13 : a 17 ∈ [0] := remove (a 17) 6 [0,6] t7 b13
  exact And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t9 (And.intro t13 (And.intro t8 (And.intro t10 (And.intro t11 (t12)))))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_186
