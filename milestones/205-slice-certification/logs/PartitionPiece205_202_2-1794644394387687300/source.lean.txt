import PartitionData205_202
namespace PartitionCover205_202
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,4,6,10,11])
    (d10 : a 10 ∈ [0,8])
    (d15 : a 15 ∈ [0,1,4,5])
    (d11 : a 11 ∈ [0,4])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 26 ∈ [0,4,6,10] ∧ a 15 ∈ [0,4] ∧ a 27 ∈ [0,1,3,4] ∧ a 12 ∈ [0,2] ∧ a 28 ∈ [0,2,6,7,8,9,11] ∧ a 29 ∈ [0,1,4,5] := by
  have b0 : a 26 ≠ 11 := exclude [0,8] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,4,6,10] := remove (a 26) 11 [0,4,6,10,11] d26 b0
  have b1 : a 15 ≠ 1 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [0,4,5] := remove (a 15) 1 [0,1,4,5] d15 b1
  have b2 : a 15 ≠ 5 := exclude [0,4] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,4] := remove (a 15) 5 [0,4,5] t1 b2
  have b3 : a 27 ≠ 2 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,3,4,5] := remove (a 27) 2 [0,1,2,3,4,5] d27 b3
  have b4 : a 27 ≠ 5 := exclude [0,4] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,3,4] := remove (a 27) 5 [0,1,3,4,5] t3 b4
  have b5 : a 12 ≠ 1 := exclude [0,2] (edge r40) (a 12) (a 13) 1 d13 c40 (by decide +kernel)
  have t5 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b5
  have b6 : a 12 ≠ 3 := exclude [0,2] (edge r40) (a 12) (a 13) 3 d13 c40 (by decide +kernel)
  have t6 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t5 b6
  have b7 : a 28 ≠ 1 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 1 t6 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b7
  have b8 : a 28 ≠ 3 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 3 t6 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 28) 3 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 28 ≠ 4 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 4 t6 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 28) 4 [0,2,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 28 ≠ 5 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 5 t6 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,6,7,8,9,10,11] := remove (a 28) 5 [0,2,5,6,7,8,9,10,11] t9 b10
  have b11 : a 28 ≠ 10 := exclude [0,2] (fun u v => edge r42 v u) (a 28) (a 12) 10 t6 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,6,7,8,9,11] := remove (a 28) 10 [0,2,6,7,8,9,10,11] t10 b11
  have b12 : a 29 ≠ 2 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,3,4,5,6,7] := remove (a 29) 2 [0,1,2,3,4,5,6,7] d29 b12
  have b13 : a 29 ≠ 3 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,4,5,6,7] := remove (a 29) 3 [0,1,3,4,5,6,7] t12 b13
  have b14 : a 29 ≠ 6 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,4,5,7] := remove (a 29) 6 [0,1,4,5,6,7] t13 b14
  have b15 : a 29 ≠ 7 := exclude [0,2] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,4,5] := remove (a 29) 7 [0,1,4,5,7] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t11 (t15)))))

theorem chunk9 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,1,8,9])
    (d31 : a 31 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,4])
    (d16 : a 16 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1,2])
    (d25 : a 25 ∈ [0,2,4,6])
    (d22 : a 22 ∈ [0,1,2,3,12,13,14,15])
    (d20 : a 20 ∈ [0,6])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    : a 30 ∈ [0,4,6,10] ∧ a 31 ∈ [0,2] ∧ a 16 ∈ [0,1] ∧ a 17 ∈ [0,2] ∧ a 25 ∈ [0,4] ∧ a 22 ∈ [0,1,3,12,13,14,15] := by
  have b0 : a 30 ≠ 1 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b0
  have b1 : a 30 ≠ 2 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 30) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 30 ≠ 3 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 30 ≠ 5 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,4,6,7,8,9,10,11] := remove (a 30) 5 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 30 ≠ 7 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,4,6,8,9,10,11] := remove (a 30) 7 [0,4,6,7,8,9,10,11] t3 b4
  have b5 : a 30 ≠ 8 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,4,6,9,10,11] := remove (a 30) 8 [0,4,6,8,9,10,11] t4 b5
  have b6 : a 30 ≠ 9 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,4,6,10,11] := remove (a 30) 9 [0,4,6,9,10,11] t5 b6
  have b7 : a 30 ≠ 11 := exclude [0,1,8,9] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,4,6,10] := remove (a 30) 11 [0,4,6,10,11] t6 b7
  have b8 : a 31 ≠ 1 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,2,3] := remove (a 31) 1 [0,1,2,3] d31 b8
  have b9 : a 31 ≠ 3 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,2] := remove (a 31) 3 [0,2,3] t8 b9
  have b10 : a 16 ≠ 2 := exclude [0,1,2] (edge r48) (a 16) (a 17) 2 d17 c48 (by decide +kernel)
  have t10 : a 16 ∈ [0,1,3] := remove (a 16) 2 [0,1,2,3] d16 b10
  have b11 : a 16 ≠ 3 := exclude [0,1,2] (edge r48) (a 16) (a 17) 3 d17 c48 (by decide +kernel)
  have t11 : a 16 ∈ [0,1] := remove (a 16) 3 [0,1,3] t10 b11
  have b12 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 1 t11 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,2] := remove (a 17) 1 [0,1,2] d17 b12
  have b13 : a 25 ≠ 2 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 2 t12 c54 (by decide +kernel)
  have t13 : a 25 ∈ [0,4,6] := remove (a 25) 2 [0,2,4,6] d25 b13
  have b14 : a 25 ≠ 6 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 6 t12 c54 (by decide +kernel)
  have t14 : a 25 ∈ [0,4] := remove (a 25) 6 [0,4,6] t13 b14
  have b15 : a 22 ≠ 2 := exclude [0,6] (fun u v => edge r61 v u) (a 22) (a 20) 2 d20 c61 (by decide +kernel)
  have t15 : a 22 ∈ [0,1,3,12,13,14,15] := remove (a 22) 2 [0,1,2,3,12,13,14,15] d22 b15
  exact And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t14 (t15)))))

theorem chunk10 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,3,12,13,14,15])
    (d20 : a 20 ∈ [0,6])
    (d28 : a 28 ∈ [0,2,6,7,8,9,11])
    (d29 : a 29 ∈ [0,1,4,5])
    (d21 : a 21 ∈ [0,3])
    (d26 : a 26 ∈ [0,4,6,10])
    (d27 : a 27 ∈ [0,1,3,4])
    (d30 : a 30 ∈ [0,4,6,10])
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 22 ∈ [0,1,12,13] ∧ a 28 ∈ [0,9] ∧ a 29 ∈ [0,4] ∧ a 26 ∈ [0,6] ∧ a 27 ∈ [0,3] ∧ a 30 ∈ [0,6] := by
  have b0 : a 22 ≠ 3 := exclude [0,6] (fun u v => edge r61 v u) (a 22) (a 20) 3 d20 c61 (by decide +kernel)
  have t0 : a 22 ∈ [0,1,12,13,14,15] := remove (a 22) 3 [0,1,3,12,13,14,15] d22 b0
  have b1 : a 22 ≠ 14 := exclude [0,6] (fun u v => edge r61 v u) (a 22) (a 20) 14 d20 c61 (by decide +kernel)
  have t1 : a 22 ∈ [0,1,12,13,15] := remove (a 22) 14 [0,1,12,13,14,15] t0 b1
  have b2 : a 22 ≠ 15 := exclude [0,6] (fun u v => edge r61 v u) (a 22) (a 20) 15 d20 c61 (by decide +kernel)
  have t2 : a 22 ∈ [0,1,12,13] := remove (a 22) 15 [0,1,12,13,15] t1 b2
  have b3 : a 28 ≠ 6 := exclude [0,6] (fun u v => edge r62 v u) (a 28) (a 20) 6 d20 c62 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,7,8,9,11] := remove (a 28) 6 [0,2,6,7,8,9,11] d28 b3
  have b4 : a 28 ≠ 7 := exclude [0,6] (fun u v => edge r62 v u) (a 28) (a 20) 7 d20 c62 (by decide +kernel)
  have t4 : a 28 ∈ [0,2,8,9,11] := remove (a 28) 7 [0,2,7,8,9,11] t3 b4
  have b5 : a 28 ≠ 8 := exclude [0,6] (fun u v => edge r62 v u) (a 28) (a 20) 8 d20 c62 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,9,11] := remove (a 28) 8 [0,2,8,9,11] t4 b5
  have b6 : a 29 ≠ 1 := exclude [0,3] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t6 : a 29 ∈ [0,4,5] := remove (a 29) 1 [0,1,4,5] d29 b6
  have b7 : a 29 ≠ 5 := exclude [0,3] (fun u v => edge r64 v u) (a 29) (a 21) 5 d21 c64 (by decide +kernel)
  have t7 : a 29 ∈ [0,4] := remove (a 29) 5 [0,4,5] t6 b7
  have b8 : a 26 ≠ 4 := exclude [0,1,3,4] (edge r73) (a 26) (a 27) 4 d27 c73 (by decide +kernel)
  have t8 : a 26 ∈ [0,6,10] := remove (a 26) 4 [0,4,6,10] d26 b8
  have b9 : a 26 ≠ 10 := exclude [0,1,3,4] (edge r73) (a 26) (a 27) 10 d27 c73 (by decide +kernel)
  have t9 : a 26 ∈ [0,6] := remove (a 26) 10 [0,6,10] t8 b9
  have b10 : a 27 ≠ 1 := exclude [0,6] (fun u v => edge r73 v u) (a 27) (a 26) 1 t9 c73 (by decide +kernel)
  have t10 : a 27 ∈ [0,3,4] := remove (a 27) 1 [0,1,3,4] d27 b10
  have b11 : a 27 ≠ 4 := exclude [0,6] (fun u v => edge r73 v u) (a 27) (a 26) 4 t9 c73 (by decide +kernel)
  have t11 : a 27 ∈ [0,3] := remove (a 27) 4 [0,3,4] t10 b11
  have b12 : a 30 ≠ 4 := exclude [0,6] (fun u v => edge r74 v u) (a 30) (a 26) 4 t9 c74 (by decide +kernel)
  have t12 : a 30 ∈ [0,6,10] := remove (a 30) 4 [0,4,6,10] d30 b12
  have b13 : a 30 ≠ 10 := exclude [0,6] (fun u v => edge r74 v u) (a 30) (a 26) 10 t9 c74 (by decide +kernel)
  have t13 : a 30 ∈ [0,6] := remove (a 30) 10 [0,6,10] t12 b13
  have b14 : a 28 ≠ 2 := exclude [0,6] (edge r77) (a 28) (a 30) 2 t13 c77 (by decide +kernel)
  have t14 : a 28 ∈ [0,9,11] := remove (a 28) 2 [0,2,9,11] t5 b14
  have b15 : a 28 ≠ 11 := exclude [0,6] (edge r77) (a 28) (a 30) 11 t13 c77 (by decide +kernel)
  have t15 : a 28 ∈ [0,9] := remove (a 28) 11 [0,9,11] t14 b15
  exact And.intro t2 (And.intro t15 (And.intro t7 (And.intro t9 (And.intro t11 (t13)))))

theorem chunk11 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,8,9])
    (d30 : a 30 ∈ [0,6])
    (d22 : a 22 ∈ [0,1,12,13])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 14 ∈ [0,8] ∧ a 22 ∈ [0,12] := by
  have b0 : a 14 ≠ 1 := exclude [0,6] (edge r46) (a 14) (a 30) 1 d30 c46 (by decide +kernel)
  have t0 : a 14 ∈ [0,8,9] := remove (a 14) 1 [0,1,8,9] d14 b0
  have b1 : a 14 ≠ 9 := exclude [0,6] (edge r46) (a 14) (a 30) 9 d30 c46 (by decide +kernel)
  have t1 : a 14 ∈ [0,8] := remove (a 14) 9 [0,8,9] t0 b1
  have b2 : a 22 ≠ 1 := exclude [0,6] (edge r66) (a 22) (a 30) 1 d30 c66 (by decide +kernel)
  have t2 : a 22 ∈ [0,12,13] := remove (a 22) 1 [0,1,12,13] d22 b2
  have b3 : a 22 ≠ 13 := exclude [0,6] (edge r66) (a 22) (a 30) 13 d30 c66 (by decide +kernel)
  have t3 : a 22 ∈ [0,12] := remove (a 22) 13 [0,12,13] t2 b3
  exact And.intro t1 (t3)

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_202
