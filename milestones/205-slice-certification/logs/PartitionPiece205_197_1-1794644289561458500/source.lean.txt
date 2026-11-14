import PartitionData205_197
namespace PartitionCover205_197
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,3])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8])
    (d15 : a 15 ∈ [0,1])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 26 ∈ [0,2] ∧ a 27 ∈ [0,1,4,5] ∧ a 29 ∈ [0,4] ∧ a 31 ∈ [0,1,2,6,7,8] := by
  have b0 : a 26 ≠ 1 := exclude [0,1] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,2] := remove (a 26) 1 [0,1,2] d26 b0
  have b1 : a 27 ≠ 2 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b1
  have b2 : a 27 ≠ 3 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 27 ≠ 6 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 27) 6 [0,1,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 27 ≠ 7 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,4,5,8,9,10,11] := remove (a 27) 7 [0,1,4,5,7,8,9,10,11] t3 b4
  have b5 : a 27 ≠ 8 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,4,5,9,10,11] := remove (a 27) 8 [0,1,4,5,8,9,10,11] t4 b5
  have b6 : a 27 ≠ 9 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,4,5,10,11] := remove (a 27) 9 [0,1,4,5,9,10,11] t5 b6
  have b7 : a 27 ≠ 10 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,4,5,11] := remove (a 27) 10 [0,1,4,5,10,11] t6 b7
  have b8 : a 27 ≠ 11 := exclude [0,3] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,4,5] := remove (a 27) 11 [0,1,4,5,11] t7 b8
  have b9 : a 29 ≠ 1 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,2,3,4,5] := remove (a 29) 1 [0,1,2,3,4,5] d29 b9
  have b10 : a 29 ≠ 2 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,3,4,5] := remove (a 29) 2 [0,2,3,4,5] t9 b10
  have b11 : a 29 ≠ 3 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,4,5] := remove (a 29) 3 [0,3,4,5] t10 b11
  have b12 : a 29 ≠ 5 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,4] := remove (a 29) 5 [0,4,5] t11 b12
  have b13 : a 31 ≠ 3 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,2,4,5,6,7,8] := remove (a 31) 3 [0,1,2,3,4,5,6,7,8] d31 b13
  have b14 : a 31 ≠ 4 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,2,5,6,7,8] := remove (a 31) 4 [0,1,2,4,5,6,7,8] t13 b14
  have b15 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,6,7,8] := remove (a 31) 5 [0,1,2,5,6,7,8] t14 b15
  exact And.intro t0 (And.intro t8 (And.intro t12 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,6,7,8])
    (d15 : a 15 ∈ [0,1])
    (d24 : a 24 ∈ [0,2,4,6,8,10])
    (d16 : a 16 ∈ [0,4])
    (d21 : a 21 ∈ [0,1,4,5])
    (d17 : a 17 ∈ [0,4])
    (d25 : a 25 ∈ [0,1,2])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    : a 31 ∈ [0,1,2] ∧ a 24 ∈ [0,8] ∧ a 21 ∈ [0,4] ∧ a 25 ∈ [0,2] ∧ a 19 ∈ [0,4,8,9,10,11] := by
  have b0 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,7,8] := remove (a 31) 6 [0,1,2,6,7,8] d31 b0
  have b1 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,2,8] := remove (a 31) 7 [0,1,2,7,8] t0 b1
  have b2 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,2] := remove (a 31) 8 [0,1,2,8] t1 b2
  have b3 : a 24 ≠ 2 := exclude [0,4] (fun u v => edge r51 v u) (a 24) (a 16) 2 d16 c51 (by decide +kernel)
  have t3 : a 24 ∈ [0,4,6,8,10] := remove (a 24) 2 [0,2,4,6,8,10] d24 b3
  have b4 : a 24 ≠ 4 := exclude [0,4] (fun u v => edge r51 v u) (a 24) (a 16) 4 d16 c51 (by decide +kernel)
  have t4 : a 24 ∈ [0,6,8,10] := remove (a 24) 4 [0,4,6,8,10] t3 b4
  have b5 : a 24 ≠ 6 := exclude [0,4] (fun u v => edge r51 v u) (a 24) (a 16) 6 d16 c51 (by decide +kernel)
  have t5 : a 24 ∈ [0,8,10] := remove (a 24) 6 [0,6,8,10] t4 b5
  have b6 : a 24 ≠ 10 := exclude [0,4] (fun u v => edge r51 v u) (a 24) (a 16) 10 d16 c51 (by decide +kernel)
  have t6 : a 24 ∈ [0,8] := remove (a 24) 10 [0,8,10] t5 b6
  have b7 : a 21 ≠ 1 := exclude [0,4] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0,4,5] := remove (a 21) 1 [0,1,4,5] d21 b7
  have b8 : a 21 ≠ 5 := exclude [0,4] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0,4] := remove (a 21) 5 [0,4,5] t7 b8
  have b9 : a 25 ≠ 1 := exclude [0,4] (fun u v => edge r54 v u) (a 25) (a 17) 1 d17 c54 (by decide +kernel)
  have t9 : a 25 ∈ [0,2] := remove (a 25) 1 [0,1,2] d25 b9
  have b10 : a 19 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b10
  have b11 : a 19 ≠ 2 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t11 : a 19 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 19) 2 [0,2,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 19 ≠ 3 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 19 ≠ 5 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0,4,6,7,8,9,10,11] := remove (a 19) 5 [0,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 19 ≠ 6 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 6 d18 c55 (by decide +kernel)
  have t14 : a 19 ∈ [0,4,7,8,9,10,11] := remove (a 19) 6 [0,4,6,7,8,9,10,11] t13 b14
  have b15 : a 19 ≠ 7 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t15 : a 19 ∈ [0,4,8,9,10,11] := remove (a 19) 7 [0,4,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t8 (And.intro t9 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,4,8,9,10,11])
    (d18 : a 18 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d28 : a 28 ∈ [0,1,2])
    (d20 : a 20 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,2])
    (c55 : edge r55 (a 18) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 19 ∈ [0,4] ∧ a 23 ∈ [0,4] ∧ a 28 ∈ [0,1] ∧ a 30 ∈ [0,2,3,4,5] := by
  have b0 : a 19 ≠ 8 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 8 d18 c55 (by decide +kernel)
  have t0 : a 19 ∈ [0,4,9,10,11] := remove (a 19) 8 [0,4,8,9,10,11] d19 b0
  have b1 : a 19 ≠ 9 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 9 d18 c55 (by decide +kernel)
  have t1 : a 19 ∈ [0,4,10,11] := remove (a 19) 9 [0,4,9,10,11] t0 b1
  have b2 : a 19 ≠ 10 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 10 d18 c55 (by decide +kernel)
  have t2 : a 19 ∈ [0,4,11] := remove (a 19) 10 [0,4,10,11] t1 b2
  have b3 : a 19 ≠ 11 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 11 d18 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,4] := remove (a 19) 11 [0,4,11] t2 b3
  have b4 : a 23 ≠ 1 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 1 t3 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b4
  have b5 : a 23 ≠ 2 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 2 t3 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 23) 2 [0,2,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 23 ≠ 3 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 3 t3 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 23 ≠ 5 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 5 t3 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,4,6,7,8,9,10,11] := remove (a 23) 5 [0,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 23 ≠ 6 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 6 t3 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,4,7,8,9,10,11] := remove (a 23) 6 [0,4,6,7,8,9,10,11] t7 b8
  have b9 : a 23 ≠ 7 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 7 t3 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,4,8,9,10,11] := remove (a 23) 7 [0,4,7,8,9,10,11] t8 b9
  have b10 : a 23 ≠ 8 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 8 t3 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,4,9,10,11] := remove (a 23) 8 [0,4,8,9,10,11] t9 b10
  have b11 : a 23 ≠ 9 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 9 t3 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,4,10,11] := remove (a 23) 9 [0,4,9,10,11] t10 b11
  have b12 : a 23 ≠ 10 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 10 t3 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,4,11] := remove (a 23) 10 [0,4,10,11] t11 b12
  have b13 : a 23 ≠ 11 := exclude [0,4] (fun u v => edge r58 v u) (a 23) (a 19) 11 t3 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,4] := remove (a 23) 11 [0,4,11] t12 b13
  have b14 : a 28 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 2 d20 c62 (by decide +kernel)
  have t14 : a 28 ∈ [0,1] := remove (a 28) 2 [0,1,2] d28 b14
  have b15 : a 30 ≠ 1 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,3,4,5] := remove (a 30) 1 [0,1,2,3,4,5] d30 b15
  exact And.intro t3 (And.intro t13 (And.intro t14 (t15)))

theorem chunk7 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,3,4,5])
    (d22 : a 22 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2])
    (d23 : a 23 ∈ [0,4])
    (d27 : a 27 ∈ [0,1,4,5])
    (d25 : a 25 ∈ [0,2])
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    : a 30 ∈ [0,2] ∧ a 31 ∈ [0] ∧ a 27 ∈ [0,4] := by
  have b0 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 3 d22 c66 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,4,5] := remove (a 30) 3 [0,2,3,4,5] d30 b0
  have b1 : a 30 ≠ 4 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 4 d22 c66 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,5] := remove (a 30) 4 [0,2,4,5] t0 b1
  have b2 : a 30 ≠ 5 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 5 d22 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0,2] := remove (a 30) 5 [0,2,5] t1 b2
  have b3 : a 31 ≠ 1 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 1 d23 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,2] := remove (a 31) 1 [0,1,2] d31 b3
  have b4 : a 31 ≠ 2 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t4 : a 31 ∈ [0] := remove (a 31) 2 [0,2] t3 b4
  have b5 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r71 v u) (a 27) (a 25) 1 d25 c71 (by decide +kernel)
  have t5 : a 27 ∈ [0,4,5] := remove (a 27) 1 [0,1,4,5] d27 b5
  have b6 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r71 v u) (a 27) (a 25) 5 d25 c71 (by decide +kernel)
  have t6 : a 27 ∈ [0,4] := remove (a 27) 5 [0,4,5] t5 b6
  exact And.intro t2 (And.intro t4 (t6))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_197
