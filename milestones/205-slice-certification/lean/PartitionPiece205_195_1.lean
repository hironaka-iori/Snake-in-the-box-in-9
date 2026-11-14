import PartitionData205_195
namespace PartitionCover205_195
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,2,3,10,11,12,13,14,15,16,17])
    (d11 : a 11 ∈ [0,6])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8])
    (d13 : a 13 ∈ [0,1])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 27 ∈ [0,1,2,3] ∧ a 28 ∈ [0,4,5,7] ∧ a 29 ∈ [0,2,4,6,7,8] := by
  have b0 : a 27 ≠ 10 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,2,3,11,12,13,14,15,16,17] := remove (a 27) 10 [0,1,2,3,10,11,12,13,14,15,16,17] d27 b0
  have b1 : a 27 ≠ 11 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,2,3,12,13,14,15,16,17] := remove (a 27) 11 [0,1,2,3,11,12,13,14,15,16,17] t0 b1
  have b2 : a 27 ≠ 12 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 12 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,2,3,13,14,15,16,17] := remove (a 27) 12 [0,1,2,3,12,13,14,15,16,17] t1 b2
  have b3 : a 27 ≠ 13 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 13 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,2,3,14,15,16,17] := remove (a 27) 13 [0,1,2,3,13,14,15,16,17] t2 b3
  have b4 : a 27 ≠ 14 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 14 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,2,3,15,16,17] := remove (a 27) 14 [0,1,2,3,14,15,16,17] t3 b4
  have b5 : a 27 ≠ 15 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 15 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,2,3,16,17] := remove (a 27) 15 [0,1,2,3,15,16,17] t4 b5
  have b6 : a 27 ≠ 16 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 16 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,2,3,17] := remove (a 27) 16 [0,1,2,3,16,17] t5 b6
  have b7 : a 27 ≠ 17 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 17 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,2,3] := remove (a 27) 17 [0,1,2,3,17] t6 b7
  have b8 : a 28 ≠ 1 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,2,3,4,5,6,7,8] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8] d28 b8
  have b9 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,3,4,5,6,7,8] := remove (a 28) 2 [0,2,3,4,5,6,7,8] t8 b9
  have b10 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,4,5,6,7,8] := remove (a 28) 3 [0,3,4,5,6,7,8] t9 b10
  have b11 : a 28 ≠ 6 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,4,5,7,8] := remove (a 28) 6 [0,4,5,6,7,8] t10 b11
  have b12 : a 28 ≠ 8 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,4,5,7] := remove (a 28) 8 [0,4,5,7,8] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,3,4,5,6,7,8] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,2,4,5,6,7,8] := remove (a 29) 3 [0,2,3,4,5,6,7,8] t13 b14
  have b15 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,4,6,7,8] := remove (a 29) 5 [0,2,4,5,6,7,8] t14 b15
  exact And.intro t7 (And.intro t12 (t15))

theorem chunk5 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,4,6,7,8])
    (d13 : a 13 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,2])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 29 ∈ [0,2,4,8] ∧ a 15 ∈ [0,2] ∧ a 30 ∈ [0,1,4,5] ∧ a 31 ∈ [0,2,3,6,9,10,13,15,16,17] := by
  have b0 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,4,7,8] := remove (a 29) 6 [0,2,4,6,7,8] d29 b0
  have b1 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,2,4,8] := remove (a 29) 7 [0,2,4,7,8] t0 b1
  have b2 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r45 v u) (a 15) (a 14) 1 d14 c45 (by decide +kernel)
  have t2 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b2
  have b3 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r45 v u) (a 15) (a 14) 3 d14 c45 (by decide +kernel)
  have t3 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t2 b3
  have b4 : a 30 ≠ 2 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,3,4,5,6,7] := remove (a 30) 2 [0,1,2,3,4,5,6,7] d30 b4
  have b5 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,4,5,6,7] := remove (a 30) 3 [0,1,3,4,5,6,7] t4 b5
  have b6 : a 30 ≠ 6 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,4,5,7] := remove (a 30) 6 [0,1,4,5,6,7] t5 b6
  have b7 : a 30 ≠ 7 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,4,5] := remove (a 30) 7 [0,1,4,5,7] t6 b7
  have b8 : a 31 ≠ 1 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 1 t3 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d31 b8
  have b9 : a 31 ≠ 4 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 4 t3 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 4 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 31 ≠ 5 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 5 t3 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,2,3,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 5 [0,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 31 ≠ 7 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 7 t3 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,2,3,6,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 7 [0,2,3,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 31 ≠ 8 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 8 t3 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,2,3,6,9,10,11,12,13,14,15,16,17] := remove (a 31) 8 [0,2,3,6,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 31 ≠ 11 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 11 t3 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,3,6,9,10,12,13,14,15,16,17] := remove (a 31) 11 [0,2,3,6,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 31 ≠ 12 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 12 t3 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,3,6,9,10,13,14,15,16,17] := remove (a 31) 12 [0,2,3,6,9,10,12,13,14,15,16,17] t13 b14
  have b15 : a 31 ≠ 14 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 14 t3 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,2,3,6,9,10,13,15,16,17] := remove (a 31) 14 [0,2,3,6,9,10,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t7 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,2,3,6,9,10,13,15,16,17])
    (d15 : a 15 ∈ [0,2])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0,1,10,11,12,13,18,19])
    (d24 : a 24 ∈ [0,2,3,8])
    (d21 : a 21 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,8,9,10,11,12])
    (d18 : a 18 ∈ [0,4,5,7,8,11])
    (d22 : a 22 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1,2,3,7,9,11])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 31 ∈ [0,2,3,6,9,10,13,15] ∧ a 17 ∈ [0,3] ∧ a 16 ∈ [0,1,12,13] ∧ a 19 ∈ [0,2,3,4,5,6,9,10,11,12] ∧ a 22 ∈ [0,2] ∧ a 26 ∈ [0,2,7,9,11] := by
  have b0 : a 31 ≠ 16 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,2,3,6,9,10,13,15,17] := remove (a 31) 16 [0,2,3,6,9,10,13,15,16,17] d31 b0
  have b1 : a 31 ≠ 17 := exclude [0,2] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,2,3,6,9,10,13,15] := remove (a 31) 17 [0,2,3,6,9,10,13,15,17] t0 b1
  have b2 : a 17 ≠ 1 := exclude [0,1,10,11,12,13,18,19] (fun u v => edge r48 v u) (a 17) (a 16) 1 d16 c48 (by decide +kernel)
  have t2 : a 17 ∈ [0,2,3,4,5] := remove (a 17) 1 [0,1,2,3,4,5] d17 b2
  have b3 : a 17 ≠ 4 := exclude [0,1,10,11,12,13,18,19] (fun u v => edge r48 v u) (a 17) (a 16) 4 d16 c48 (by decide +kernel)
  have t3 : a 17 ∈ [0,2,3,5] := remove (a 17) 4 [0,2,3,4,5] t2 b3
  have b4 : a 16 ≠ 10 := exclude [0,2,3,8] (edge r51) (a 16) (a 24) 10 d24 c51 (by decide +kernel)
  have t4 : a 16 ∈ [0,1,11,12,13,18,19] := remove (a 16) 10 [0,1,10,11,12,13,18,19] d16 b4
  have b5 : a 16 ≠ 11 := exclude [0,2,3,8] (edge r51) (a 16) (a 24) 11 d24 c51 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,12,13,18,19] := remove (a 16) 11 [0,1,11,12,13,18,19] t4 b5
  have b6 : a 16 ≠ 18 := exclude [0,2,3,8] (edge r51) (a 16) (a 24) 18 d24 c51 (by decide +kernel)
  have t6 : a 16 ∈ [0,1,12,13,19] := remove (a 16) 18 [0,1,12,13,18,19] t5 b6
  have b7 : a 16 ≠ 19 := exclude [0,2,3,8] (edge r51) (a 16) (a 24) 19 d24 c51 (by decide +kernel)
  have t7 : a 16 ∈ [0,1,12,13] := remove (a 16) 19 [0,1,12,13,19] t6 b7
  have b8 : a 17 ≠ 2 := exclude [0,1] (edge r53) (a 17) (a 21) 2 d21 c53 (by decide +kernel)
  have t8 : a 17 ∈ [0,3,5] := remove (a 17) 2 [0,2,3,5] t3 b8
  have b9 : a 17 ≠ 5 := exclude [0,1] (edge r53) (a 17) (a 21) 5 d21 c53 (by decide +kernel)
  have t9 : a 17 ∈ [0,3] := remove (a 17) 5 [0,3,5] t8 b9
  have b10 : a 19 ≠ 1 := exclude [0,4,5,7,8,11] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,2,3,4,5,6,8,9,10,11,12] := remove (a 19) 1 [0,1,2,3,4,5,6,8,9,10,11,12] d19 b10
  have b11 : a 19 ≠ 8 := exclude [0,4,5,7,8,11] (fun u v => edge r55 v u) (a 19) (a 18) 8 d18 c55 (by decide +kernel)
  have t11 : a 19 ∈ [0,2,3,4,5,6,9,10,11,12] := remove (a 19) 8 [0,2,3,4,5,6,8,9,10,11,12] t10 b11
  have b12 : a 22 ≠ 1 := exclude [0,4,5,7,8,11] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b12
  have b13 : a 22 ≠ 3 := exclude [0,4,5,7,8,11] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t12 b13
  have b14 : a 26 ≠ 1 := exclude [0,4,5,7,8,11] (fun u v => edge r57 v u) (a 26) (a 18) 1 d18 c57 (by decide +kernel)
  have t14 : a 26 ∈ [0,2,3,7,9,11] := remove (a 26) 1 [0,1,2,3,7,9,11] d26 b14
  have b15 : a 26 ≠ 3 := exclude [0,4,5,7,8,11] (fun u v => edge r57 v u) (a 26) (a 18) 3 d18 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0,2,7,9,11] := remove (a 26) 3 [0,2,3,7,9,11] t14 b15
  exact And.intro t1 (And.intro t9 (And.intro t7 (And.intro t11 (And.intro t13 (t15)))))

theorem chunk7 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,2,7,9,11])
    (d18 : a 18 ∈ [0,4,5,7,8,11])
    (d19 : a 19 ∈ [0,2,3,4,5,6,9,10,11,12])
    (d23 : a 23 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,4,5,7])
    (d20 : a 20 ∈ [0,1])
    (d31 : a 31 ∈ [0,2,3,6,9,10,13,15])
    (d25 : a 25 ∈ [0,1,2,3,4,6,8,9,10,13,15,17])
    (d24 : a 24 ∈ [0,2,3,8])
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 26 ∈ [0,2,9,11] ∧ a 19 ∈ [0,3] ∧ a 28 ∈ [0,7] ∧ a 31 ∈ [0,2,3,9] ∧ a 25 ∈ [0,2,3,4,6,8,9,10,13,15,17] := by
  have b0 : a 26 ≠ 7 := exclude [0,4,5,7,8,11] (fun u v => edge r57 v u) (a 26) (a 18) 7 d18 c57 (by decide +kernel)
  have t0 : a 26 ∈ [0,2,9,11] := remove (a 26) 7 [0,2,7,9,11] d26 b0
  have b1 : a 19 ≠ 4 := exclude [0,2] (edge r58) (a 19) (a 23) 4 d23 c58 (by decide +kernel)
  have t1 : a 19 ∈ [0,2,3,5,6,9,10,11,12] := remove (a 19) 4 [0,2,3,4,5,6,9,10,11,12] d19 b1
  have b2 : a 19 ≠ 5 := exclude [0,2] (edge r58) (a 19) (a 23) 5 d23 c58 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3,6,9,10,11,12] := remove (a 19) 5 [0,2,3,5,6,9,10,11,12] t1 b2
  have b3 : a 19 ≠ 6 := exclude [0,2] (edge r58) (a 19) (a 23) 6 d23 c58 (by decide +kernel)
  have t3 : a 19 ∈ [0,2,3,9,10,11,12] := remove (a 19) 6 [0,2,3,6,9,10,11,12] t2 b3
  have b4 : a 19 ≠ 10 := exclude [0,2] (edge r58) (a 19) (a 23) 10 d23 c58 (by decide +kernel)
  have t4 : a 19 ∈ [0,2,3,9,11,12] := remove (a 19) 10 [0,2,3,9,10,11,12] t3 b4
  have b5 : a 19 ≠ 11 := exclude [0,2] (edge r58) (a 19) (a 23) 11 d23 c58 (by decide +kernel)
  have t5 : a 19 ∈ [0,2,3,9,12] := remove (a 19) 11 [0,2,3,9,11,12] t4 b5
  have b6 : a 19 ≠ 12 := exclude [0,2] (edge r58) (a 19) (a 23) 12 d23 c58 (by decide +kernel)
  have t6 : a 19 ∈ [0,2,3,9] := remove (a 19) 12 [0,2,3,9,12] t5 b6
  have b7 : a 19 ≠ 2 := exclude [0,1,2,3] (edge r59) (a 19) (a 27) 2 d27 c59 (by decide +kernel)
  have t7 : a 19 ∈ [0,3,9] := remove (a 19) 2 [0,2,3,9] t6 b7
  have b8 : a 19 ≠ 9 := exclude [0,1,2,3] (edge r59) (a 19) (a 27) 9 d27 c59 (by decide +kernel)
  have t8 : a 19 ∈ [0,3] := remove (a 19) 9 [0,3,9] t7 b8
  have b9 : a 28 ≠ 4 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 4 d20 c62 (by decide +kernel)
  have t9 : a 28 ∈ [0,5,7] := remove (a 28) 4 [0,4,5,7] d28 b9
  have b10 : a 28 ≠ 5 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 5 d20 c62 (by decide +kernel)
  have t10 : a 28 ∈ [0,7] := remove (a 28) 5 [0,5,7] t9 b10
  have b11 : a 31 ≠ 6 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 6 d23 c67 (by decide +kernel)
  have t11 : a 31 ∈ [0,2,3,9,10,13,15] := remove (a 31) 6 [0,2,3,6,9,10,13,15] d31 b11
  have b12 : a 31 ≠ 10 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 10 d23 c67 (by decide +kernel)
  have t12 : a 31 ∈ [0,2,3,9,13,15] := remove (a 31) 10 [0,2,3,9,10,13,15] t11 b12
  have b13 : a 31 ≠ 13 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 13 d23 c67 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,3,9,15] := remove (a 31) 13 [0,2,3,9,13,15] t12 b13
  have b14 : a 31 ≠ 15 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 15 d23 c67 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,3,9] := remove (a 31) 15 [0,2,3,9,15] t13 b14
  have b15 : a 25 ≠ 1 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t15 : a 25 ∈ [0,2,3,4,6,8,9,10,13,15,17] := remove (a 25) 1 [0,1,2,3,4,6,8,9,10,13,15,17] d25 b15
  exact And.intro t0 (And.intro t8 (And.intro t10 (And.intro t14 (t15))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_195
