import PartitionData205_171
namespace PartitionCover205_171
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,2,3,4,5])
    (d9 : a 9 ∈ [0,3])
    (d14 : a 14 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,4])
    (d26 : a 26 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,6])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 25 ∈ [0,3] ∧ a 14 ∈ [0,2] ∧ a 26 ∈ [0,2] ∧ a 15 ∈ [0,3] ∧ a 27 ∈ [0,1,6,7] := by
  have b0 : a 25 ≠ 2 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,3,4,5] := remove (a 25) 2 [0,2,3,4,5] d25 b0
  have b1 : a 25 ≠ 4 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,3,5] := remove (a 25) 4 [0,3,4,5] t0 b1
  have b2 : a 25 ≠ 5 := exclude [0,3] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,3] := remove (a 25) 5 [0,3,5] t1 b2
  have b3 : a 14 ≠ 1 := exclude [0,4] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,2] := remove (a 14) 1 [0,1,2] d14 b3
  have b4 : a 26 ≠ 1 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b4
  have b5 : a 26 ≠ 3 := exclude [0,4] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,2] := remove (a 26) 3 [0,2,3] t4 b5
  have b6 : a 15 ≠ 1 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b6
  have b7 : a 15 ≠ 2 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,3] := remove (a 15) 2 [0,2,3] t6 b7
  have b8 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b8
  have b9 : a 27 ≠ 3 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 4 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,6,7,9,10,11] := remove (a 27) 8 [0,1,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 9 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,6,7,10,11] := remove (a 27) 9 [0,1,6,7,9,10,11] t12 b13
  have b14 : a 27 ≠ 10 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,6,7,11] := remove (a 27) 10 [0,1,6,7,10,11] t13 b14
  have b15 : a 27 ≠ 11 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,6,7] := remove (a 27) 11 [0,1,6,7,11] t14 b15
  exact And.intro t2 (And.intro t3 (And.intro t5 (And.intro t7 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (d14 : a 14 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8])
    (d15 : a 15 ∈ [0,3])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 28 ∈ [0,4] ∧ a 29 ∈ [0,4] ∧ a 30 ∈ [0,1,2,4,5,6] ∧ a 31 ∈ [0,1,2,5,6,7,8] := by
  have b0 : a 28 ≠ 1 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,3,4,5,6,7] := remove (a 28) 1 [0,1,2,3,4,5,6,7] d28 b0
  have b1 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,3,4,5,6,7] := remove (a 28) 2 [0,2,3,4,5,6,7] t0 b1
  have b2 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,4,5,6,7] := remove (a 28) 3 [0,3,4,5,6,7] t1 b2
  have b3 : a 28 ≠ 5 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,4,6,7] := remove (a 28) 5 [0,4,5,6,7] t2 b3
  have b4 : a 28 ≠ 6 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,4,7] := remove (a 28) 6 [0,4,6,7] t3 b4
  have b5 : a 28 ≠ 7 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,4] := remove (a 28) 7 [0,4,7] t4 b5
  have b6 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,2,3,4,5,6,7] := remove (a 29) 1 [0,1,2,3,4,5,6,7] d29 b6
  have b7 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,3,4,5,6,7] := remove (a 29) 2 [0,2,3,4,5,6,7] t6 b7
  have b8 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,4,5,6,7] := remove (a 29) 3 [0,3,4,5,6,7] t7 b8
  have b9 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,4,6,7] := remove (a 29) 5 [0,4,5,6,7] t8 b9
  have b10 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,4,7] := remove (a 29) 6 [0,4,6,7] t9 b10
  have b11 : a 29 ≠ 7 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,4] := remove (a 29) 7 [0,4,7] t10 b11
  have b12 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,2,4,5,6,7] := remove (a 30) 3 [0,1,2,3,4,5,6,7] d30 b12
  have b13 : a 30 ≠ 7 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,2,4,5,6] := remove (a 30) 7 [0,1,2,4,5,6,7] t12 b13
  have b14 : a 31 ≠ 3 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,2,4,5,6,7,8] := remove (a 31) 3 [0,1,2,3,4,5,6,7,8] d31 b14
  have b15 : a 31 ≠ 4 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,5,6,7,8] := remove (a 31) 4 [0,1,2,4,5,6,7,8] t14 b15
  exact And.intro t5 (And.intro t11 (And.intro t13 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,5,6,7,8])
    (d15 : a 15 ∈ [0,3])
    (d20 : a 20 ∈ [0,3])
    (d16 : a 16 ∈ [0,2])
    (d22 : a 22 ∈ [0,1,2])
    (d18 : a 18 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,6,7])
    (d30 : a 30 ∈ [0,1,2,4,5,6])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 31 ∈ [0,1,2,6,7,8] ∧ a 20 ∈ [0] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0,5] ∧ a 27 ∈ [0,1] ∧ a 30 ∈ [0,4] := by
  have b0 : a 31 ≠ 5 := exclude [0,3] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,6,7,8] := remove (a 31) 5 [0,1,2,5,6,7,8] d31 b0
  have b1 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r50 v u) (a 20) (a 16) 3 d16 c50 (by decide +kernel)
  have t1 : a 20 ∈ [0] := remove (a 20) 3 [0,3] d20 b1
  have b2 : a 22 ≠ 1 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t2 : a 22 ∈ [0,2] := remove (a 22) 1 [0,1,2] d22 b2
  have b3 : a 22 ≠ 2 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 2 d18 c56 (by decide +kernel)
  have t3 : a 22 ∈ [0] := remove (a 22) 2 [0,2] t2 b3
  have b4 : a 23 ≠ 1 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,2,3,4,5,6,7] := remove (a 23) 1 [0,1,2,3,4,5,6,7] d23 b4
  have b5 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,3,4,5,6,7] := remove (a 23) 2 [0,2,3,4,5,6,7] t4 b5
  have b6 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,4,5,6,7] := remove (a 23) 3 [0,3,4,5,6,7] t5 b6
  have b7 : a 23 ≠ 4 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,5,6,7] := remove (a 23) 4 [0,4,5,6,7] t6 b7
  have b8 : a 23 ≠ 6 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 6 d19 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,5,7] := remove (a 23) 6 [0,5,6,7] t7 b8
  have b9 : a 23 ≠ 7 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,5] := remove (a 23) 7 [0,5,7] t8 b9
  have b10 : a 27 ≠ 6 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 6 d19 c59 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,7] := remove (a 27) 6 [0,1,6,7] d27 b10
  have b11 : a 27 ≠ 7 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 7 d19 c59 (by decide +kernel)
  have t11 : a 27 ∈ [0,1] := remove (a 27) 7 [0,1,7] t10 b11
  have b12 : a 30 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 1 t3 c66 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,4,5,6] := remove (a 30) 1 [0,1,2,4,5,6] d30 b12
  have b13 : a 30 ≠ 2 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 2 t3 c66 (by decide +kernel)
  have t13 : a 30 ∈ [0,4,5,6] := remove (a 30) 2 [0,2,4,5,6] t12 b13
  have b14 : a 30 ≠ 5 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 5 t3 c66 (by decide +kernel)
  have t14 : a 30 ∈ [0,4,6] := remove (a 30) 5 [0,4,5,6] t13 b14
  have b15 : a 30 ≠ 6 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 6 t3 c66 (by decide +kernel)
  have t15 : a 30 ∈ [0,4] := remove (a 30) 6 [0,4,6] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t9 (And.intro t11 (t15)))))

theorem chunk7 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1])
    (d26 : a 26 ∈ [0,2])
    (d25 : a 25 ∈ [0,3])
    (d27 : a 27 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,6,7,8])
    (d29 : a 29 ∈ [0,4])
    (c69 : edge r69 (a 24) (a 26)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 31 ∈ [0,6] := by
  have b0 : a 24 ≠ 1 := exclude [0,2] (edge r69) (a 24) (a 26) 1 d26 c69 (by decide +kernel)
  have t0 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b0
  have b1 : a 25 ≠ 3 := exclude [0,1] (edge r71) (a 25) (a 27) 3 d27 c71 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 3 [0,3] d25 b1
  have b2 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r75 v u) (a 31) (a 27) 2 d27 c75 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,6,7,8] := remove (a 31) 2 [0,1,2,6,7,8] d31 b2
  have b3 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r75 v u) (a 31) (a 27) 8 d27 c75 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,6,7] := remove (a 31) 8 [0,1,6,7,8] t2 b3
  have b4 : a 31 ≠ 1 := exclude [0,4] (fun u v => edge r78 v u) (a 31) (a 29) 1 d29 c78 (by decide +kernel)
  have t4 : a 31 ∈ [0,6,7] := remove (a 31) 1 [0,1,6,7] t3 b4
  have b5 : a 31 ≠ 7 := exclude [0,4] (fun u v => edge r78 v u) (a 31) (a 29) 7 d29 c78 (by decide +kernel)
  have t5 : a 31 ∈ [0,6] := remove (a 31) 7 [0,6,7] t4 b5
  exact And.intro t0 (And.intro t1 (t5))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_171
