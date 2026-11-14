import PartitionData205_182
namespace PartitionCover205_182
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d18 : a 18 ∈ [0])
    (c55 : edge r55 (a 18) (a 19)=true)
    : a 19 ∈ [0,1] := by
  have b0 : a 19 ≠ 2 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d19 b0
  have b1 : a 19 ≠ 3 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 19 ≠ 4 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 4 d18 c55 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 19 ≠ 5 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 19 ≠ 6 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 6 d18 c55 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 19 ≠ 7 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t5 : a 19 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 19) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 19 ≠ 8 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 8 d18 c55 (by decide +kernel)
  have t6 : a 19 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 19) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 19 ≠ 9 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 9 d18 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 19) 9 [0,1,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 19 ≠ 10 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 10 d18 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 19) 10 [0,1,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 19 ≠ 11 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 11 d18 c55 (by decide +kernel)
  have t9 : a 19 ∈ [0,1,12,13,14,15,16,17] := remove (a 19) 11 [0,1,11,12,13,14,15,16,17] t8 b9
  have b10 : a 19 ≠ 12 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 12 d18 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,1,13,14,15,16,17] := remove (a 19) 12 [0,1,12,13,14,15,16,17] t9 b10
  have b11 : a 19 ≠ 13 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 13 d18 c55 (by decide +kernel)
  have t11 : a 19 ∈ [0,1,14,15,16,17] := remove (a 19) 13 [0,1,13,14,15,16,17] t10 b11
  have b12 : a 19 ≠ 14 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 14 d18 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0,1,15,16,17] := remove (a 19) 14 [0,1,14,15,16,17] t11 b12
  have b13 : a 19 ≠ 15 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 15 d18 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0,1,16,17] := remove (a 19) 15 [0,1,15,16,17] t12 b13
  have b14 : a 19 ≠ 16 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 16 d18 c55 (by decide +kernel)
  have t14 : a 19 ∈ [0,1,17] := remove (a 19) 16 [0,1,16,17] t13 b14
  have b15 : a 19 ≠ 17 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 17 d18 c55 (by decide +kernel)
  have t15 : a 19 ∈ [0,1] := remove (a 19) 17 [0,1,17] t14 b15
  exact t15

theorem chunk13 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d18 : a 18 ∈ [0])
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 22 ∈ [0,2] := by
  have b0 : a 22 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t0 : a 22 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d22 b0
  have b1 : a 22 ≠ 3 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 22 ≠ 4 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t2 : a 22 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 22 ≠ 5 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t3 : a 22 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 22 ≠ 6 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 6 d18 c56 (by decide +kernel)
  have t4 : a 22 ∈ [0,2,7,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 6 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 22 ≠ 7 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 7 d18 c56 (by decide +kernel)
  have t5 : a 22 ∈ [0,2,8,9,10,11,12,13,14,15,16,17] := remove (a 22) 7 [0,2,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 22 ≠ 8 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 8 d18 c56 (by decide +kernel)
  have t6 : a 22 ∈ [0,2,9,10,11,12,13,14,15,16,17] := remove (a 22) 8 [0,2,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 22 ≠ 9 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 9 d18 c56 (by decide +kernel)
  have t7 : a 22 ∈ [0,2,10,11,12,13,14,15,16,17] := remove (a 22) 9 [0,2,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 22 ≠ 10 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 10 d18 c56 (by decide +kernel)
  have t8 : a 22 ∈ [0,2,11,12,13,14,15,16,17] := remove (a 22) 10 [0,2,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 22 ≠ 11 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 11 d18 c56 (by decide +kernel)
  have t9 : a 22 ∈ [0,2,12,13,14,15,16,17] := remove (a 22) 11 [0,2,11,12,13,14,15,16,17] t8 b9
  have b10 : a 22 ≠ 12 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 12 d18 c56 (by decide +kernel)
  have t10 : a 22 ∈ [0,2,13,14,15,16,17] := remove (a 22) 12 [0,2,12,13,14,15,16,17] t9 b10
  have b11 : a 22 ≠ 13 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 13 d18 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,14,15,16,17] := remove (a 22) 13 [0,2,13,14,15,16,17] t10 b11
  have b12 : a 22 ≠ 14 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 14 d18 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,15,16,17] := remove (a 22) 14 [0,2,14,15,16,17] t11 b12
  have b13 : a 22 ≠ 15 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 15 d18 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,16,17] := remove (a 22) 15 [0,2,15,16,17] t12 b13
  have b14 : a 22 ≠ 16 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 16 d18 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,17] := remove (a 22) 16 [0,2,16,17] t13 b14
  have b15 : a 22 ≠ 17 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 17 d18 c56 (by decide +kernel)
  have t15 : a 22 ∈ [0,2] := remove (a 22) 17 [0,2,17] t14 b15
  exact t15

theorem chunk14 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,2,3,5,6,8])
    (d18 : a 18 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,5,6,8])
    (d20 : a 20 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,4,5,6,7,9])
    (d21 : a 21 ∈ [0])
    (d30 : a 30 ∈ [0,2,6,8,12,14])
    (d22 : a 22 ∈ [0,2])
    (c57 : edge r57 (a 18) (a 26)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 26 ∈ [0,1] ∧ a 28 ∈ [0,1] ∧ a 29 ∈ [0,6] ∧ a 30 ∈ [0,2,8,12,14] := by
  have b0 : a 26 ≠ 2 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 2 d18 c57 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,3,5,6,8] := remove (a 26) 2 [0,1,2,3,5,6,8] d26 b0
  have b1 : a 26 ≠ 3 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 3 d18 c57 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,5,6,8] := remove (a 26) 3 [0,1,3,5,6,8] t0 b1
  have b2 : a 26 ≠ 5 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 5 d18 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,6,8] := remove (a 26) 5 [0,1,5,6,8] t1 b2
  have b3 : a 26 ≠ 6 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 6 d18 c57 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,8] := remove (a 26) 6 [0,1,6,8] t2 b3
  have b4 : a 26 ≠ 8 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 8 d18 c57 (by decide +kernel)
  have t4 : a 26 ∈ [0,1] := remove (a 26) 8 [0,1,8] t3 b4
  have b5 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 2 d20 c62 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,3,5,6,8] := remove (a 28) 2 [0,1,2,3,5,6,8] d28 b5
  have b6 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 3 d20 c62 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,5,6,8] := remove (a 28) 3 [0,1,3,5,6,8] t5 b6
  have b7 : a 28 ≠ 5 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 5 d20 c62 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,6,8] := remove (a 28) 5 [0,1,5,6,8] t6 b7
  have b8 : a 28 ≠ 6 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 6 d20 c62 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,8] := remove (a 28) 6 [0,1,6,8] t7 b8
  have b9 : a 28 ≠ 8 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 8 d20 c62 (by decide +kernel)
  have t9 : a 28 ∈ [0,1] := remove (a 28) 8 [0,1,8] t8 b9
  have b10 : a 29 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0,4,5,6,7,9] := remove (a 29) 1 [0,1,4,5,6,7,9] d29 b10
  have b11 : a 29 ≠ 4 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 4 d21 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0,5,6,7,9] := remove (a 29) 4 [0,4,5,6,7,9] t10 b11
  have b12 : a 29 ≠ 5 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 5 d21 c64 (by decide +kernel)
  have t12 : a 29 ∈ [0,6,7,9] := remove (a 29) 5 [0,5,6,7,9] t11 b12
  have b13 : a 29 ≠ 7 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 7 d21 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0,6,9] := remove (a 29) 7 [0,6,7,9] t12 b13
  have b14 : a 29 ≠ 9 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 9 d21 c64 (by decide +kernel)
  have t14 : a 29 ∈ [0,6] := remove (a 29) 9 [0,6,9] t13 b14
  have b15 : a 30 ≠ 6 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 6 d22 c66 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,8,12,14] := remove (a 30) 6 [0,2,6,8,12,14] d30 b15
  exact And.intro t4 (And.intro t9 (And.intro t14 (t15)))

theorem chunk15 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,8,12,14])
    (d22 : a 22 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d13 : a 13 ∈ [0,2,3,5])
    (d29 : a 29 ∈ [0,6])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 30 ∈ [0,2] ∧ a 31 ∈ [0] ∧ a 13 ∈ [0,3] := by
  have b0 : a 30 ≠ 8 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 8 d22 c66 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,12,14] := remove (a 30) 8 [0,2,8,12,14] d30 b0
  have b1 : a 30 ≠ 12 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 12 d22 c66 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,14] := remove (a 30) 12 [0,2,12,14] t0 b1
  have b2 : a 30 ≠ 14 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 14 d22 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0,2] := remove (a 30) 14 [0,2,14] t1 b2
  have b3 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b3
  have b4 : a 31 ≠ 3 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 3 d23 c67 (by decide +kernel)
  have t4 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t3 b4
  have b5 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r75 v u) (a 31) (a 27) 1 d27 c75 (by decide +kernel)
  have t5 : a 31 ∈ [0] := remove (a 31) 1 [0,1] t4 b5
  have b6 : a 13 ≠ 2 := exclude [0,6] (edge r44) (a 13) (a 29) 2 d29 c44 (by decide +kernel)
  have t6 : a 13 ∈ [0,3,5] := remove (a 13) 2 [0,2,3,5] d13 b6
  have b7 : a 13 ≠ 5 := exclude [0,6] (edge r44) (a 13) (a 29) 5 d29 c44 (by decide +kernel)
  have t7 : a 13 ∈ [0,3] := remove (a 13) 5 [0,3,5] t6 b7
  exact And.intro t2 (And.intro t5 (t7))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_182
