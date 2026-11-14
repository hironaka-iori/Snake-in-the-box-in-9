import PartitionData205_184
namespace PartitionCover205_184
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,2,3,10,11])
    (d11 : a 11 ∈ [0,1])
    (d28 : a 28 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8])
    (d15 : a 15 ∈ [0,1])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 27 ∈ [0,1,2,3] ∧ a 28 ∈ [0,1] ∧ a 29 ∈ [0,1,2,3] ∧ a 30 ∈ [0,2] ∧ a 31 ∈ [0,1,2,3,4,5,7,8] := by
  have b0 : a 27 ≠ 10 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,2,3,11] := remove (a 27) 10 [0,1,2,3,10,11] d27 b0
  have b1 : a 27 ≠ 11 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,2,3] := remove (a 27) 11 [0,1,2,3,11] t0 b1
  have b2 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,1] := remove (a 28) 2 [0,1,2] d28 b2
  have b3 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 29) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b3
  have b4 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 29) 5 [0,1,2,3,5,6,7,8,9,10,11] t3 b4
  have b5 : a 29 ≠ 6 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 29) 6 [0,1,2,3,6,7,8,9,10,11] t4 b5
  have b6 : a 29 ≠ 7 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,2,3,8,9,10,11] := remove (a 29) 7 [0,1,2,3,7,8,9,10,11] t5 b6
  have b7 : a 29 ≠ 8 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,2,3,9,10,11] := remove (a 29) 8 [0,1,2,3,8,9,10,11] t6 b7
  have b8 : a 29 ≠ 9 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,2,3,10,11] := remove (a 29) 9 [0,1,2,3,9,10,11] t7 b8
  have b9 : a 29 ≠ 10 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,2,3,11] := remove (a 29) 10 [0,1,2,3,10,11] t8 b9
  have b10 : a 29 ≠ 11 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,2,3] := remove (a 29) 11 [0,1,2,3,11] t9 b10
  have b11 : a 30 ≠ 1 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,3,4,5] := remove (a 30) 1 [0,1,2,3,4,5] d30 b11
  have b12 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,4,5] := remove (a 30) 3 [0,2,3,4,5] t11 b12
  have b13 : a 30 ≠ 4 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,5] := remove (a 30) 4 [0,2,4,5] t12 b13
  have b14 : a 30 ≠ 5 := exclude [0,2] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,2] := remove (a 30) 5 [0,2,5] t13 b14
  have b15 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,3,4,5,7,8] := remove (a 31) 6 [0,1,2,3,4,5,6,7,8] d31 b15
  exact And.intro t1 (And.intro t2 (And.intro t10 (And.intro t14 (t15))))

theorem chunk9 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,4,5,7,8])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [0,2,6,8,12,14])
    (d16 : a 16 ∈ [0,3])
    (d20 : a 20 ∈ [0,1,12,16])
    (d21 : a 21 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    : a 31 ∈ [0,1,2,3,4,5] ∧ a 17 ∈ [0,6] ∧ a 20 ∈ [0,1] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0,6,9,10,11] := by
  have b0 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3,4,5,8] := remove (a 31) 7 [0,1,2,3,4,5,7,8] d31 b0
  have b1 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,1,2,3,4,5] := remove (a 31) 8 [0,1,2,3,4,5,8] t0 b1
  have b2 : a 17 ≠ 2 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t2 : a 17 ∈ [0,6,8,12,14] := remove (a 17) 2 [0,2,6,8,12,14] d17 b2
  have b3 : a 17 ≠ 8 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 8 d16 c48 (by decide +kernel)
  have t3 : a 17 ∈ [0,6,12,14] := remove (a 17) 8 [0,6,8,12,14] t2 b3
  have b4 : a 17 ≠ 12 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 12 d16 c48 (by decide +kernel)
  have t4 : a 17 ∈ [0,6,14] := remove (a 17) 12 [0,6,12,14] t3 b4
  have b5 : a 17 ≠ 14 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 14 d16 c48 (by decide +kernel)
  have t5 : a 17 ∈ [0,6] := remove (a 17) 14 [0,6,14] t4 b5
  have b6 : a 20 ≠ 12 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 12 d16 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,16] := remove (a 20) 12 [0,1,12,16] d20 b6
  have b7 : a 20 ≠ 16 := exclude [0,3] (fun u v => edge r50 v u) (a 20) (a 16) 16 d16 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0,1] := remove (a 20) 16 [0,1,16] t6 b7
  have b8 : a 21 ≠ 1 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 1 t5 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b8
  have b9 : a 25 ≠ 1 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 1 t5 c54 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b9
  have b10 : a 25 ≠ 2 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 2 t5 c54 (by decide +kernel)
  have t10 : a 25 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 25 ≠ 3 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 3 t5 c54 (by decide +kernel)
  have t11 : a 25 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 25 ≠ 4 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 4 t5 c54 (by decide +kernel)
  have t12 : a 25 ∈ [0,5,6,7,8,9,10,11] := remove (a 25) 4 [0,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 25 ≠ 5 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 5 t5 c54 (by decide +kernel)
  have t13 : a 25 ∈ [0,6,7,8,9,10,11] := remove (a 25) 5 [0,5,6,7,8,9,10,11] t12 b13
  have b14 : a 25 ≠ 7 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 7 t5 c54 (by decide +kernel)
  have t14 : a 25 ∈ [0,6,8,9,10,11] := remove (a 25) 7 [0,6,7,8,9,10,11] t13 b14
  have b15 : a 25 ≠ 8 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 8 t5 c54 (by decide +kernel)
  have t15 : a 25 ∈ [0,6,9,10,11] := remove (a 25) 8 [0,6,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t7 (And.intro t8 (t15))))

theorem chunk10 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,6,9,10,11])
    (d17 : a 17 ∈ [0,6])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d18 : a 18 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 25 ∈ [0,6] ∧ a 19 ∈ [0,2] ∧ a 22 ∈ [0,2,5] := by
  have b0 : a 25 ≠ 9 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 9 d17 c54 (by decide +kernel)
  have t0 : a 25 ∈ [0,6,10,11] := remove (a 25) 9 [0,6,9,10,11] d25 b0
  have b1 : a 25 ≠ 10 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 10 d17 c54 (by decide +kernel)
  have t1 : a 25 ∈ [0,6,11] := remove (a 25) 10 [0,6,10,11] t0 b1
  have b2 : a 25 ≠ 11 := exclude [0,6] (fun u v => edge r54 v u) (a 25) (a 17) 11 d17 c54 (by decide +kernel)
  have t2 : a 25 ∈ [0,6] := remove (a 25) 11 [0,6,11] t1 b2
  have b3 : a 19 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 19) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d19 b3
  have b4 : a 19 ≠ 3 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 3 d18 c55 (by decide +kernel)
  have t4 : a 19 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 19) 3 [0,2,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 19 ≠ 4 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 4 d18 c55 (by decide +kernel)
  have t5 : a 19 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 19) 4 [0,2,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 19 ≠ 5 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t6 : a 19 ∈ [0,2,6,7,8,9,10,11] := remove (a 19) 5 [0,2,5,6,7,8,9,10,11] t5 b6
  have b7 : a 19 ≠ 6 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 6 d18 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0,2,7,8,9,10,11] := remove (a 19) 6 [0,2,6,7,8,9,10,11] t6 b7
  have b8 : a 19 ≠ 7 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,2,8,9,10,11] := remove (a 19) 7 [0,2,7,8,9,10,11] t7 b8
  have b9 : a 19 ≠ 8 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 8 d18 c55 (by decide +kernel)
  have t9 : a 19 ∈ [0,2,9,10,11] := remove (a 19) 8 [0,2,8,9,10,11] t8 b9
  have b10 : a 19 ≠ 9 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 9 d18 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,2,10,11] := remove (a 19) 9 [0,2,9,10,11] t9 b10
  have b11 : a 19 ≠ 10 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 10 d18 c55 (by decide +kernel)
  have t11 : a 19 ∈ [0,2,11] := remove (a 19) 10 [0,2,10,11] t10 b11
  have b12 : a 19 ≠ 11 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 11 d18 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0,2] := remove (a 19) 11 [0,2,11] t11 b12
  have b13 : a 22 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b13
  have b14 : a 22 ≠ 3 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,4,5] := remove (a 22) 3 [0,2,3,4,5] t13 b14
  have b15 : a 22 ≠ 4 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t15 : a 22 ∈ [0,2,5] := remove (a 22) 4 [0,2,4,5] t14 b15
  exact And.intro t2 (And.intro t12 (t15))

theorem chunk11 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,2,5])
    (d18 : a 18 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,4])
    (d27 : a 27 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,2])
    (d29 : a 29 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (d23 : a 23 ∈ [0,2])
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 22 ∈ [0,2] ∧ a 26 ∈ [0,1] ∧ a 27 ∈ [0,2] ∧ a 29 ∈ [0,2] ∧ a 31 ∈ [0,3] := by
  have b0 : a 22 ≠ 5 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t0 : a 22 ∈ [0,2] := remove (a 22) 5 [0,2,5] d22 b0
  have b1 : a 26 ≠ 2 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 2 d18 c57 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,4] := remove (a 26) 2 [0,1,2,4] d26 b1
  have b2 : a 26 ≠ 4 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 4 d18 c57 (by decide +kernel)
  have t2 : a 26 ∈ [0,1] := remove (a 26) 4 [0,1,4] t1 b2
  have b3 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t3 : a 27 ∈ [0,2,3] := remove (a 27) 1 [0,1,2,3] d27 b3
  have b4 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r59 v u) (a 27) (a 19) 3 d19 c59 (by decide +kernel)
  have t4 : a 27 ∈ [0,2] := remove (a 27) 3 [0,2,3] t3 b4
  have b5 : a 29 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t5 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b5
  have b6 : a 29 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 3 d21 c64 (by decide +kernel)
  have t6 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t5 b6
  have b7 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,3,4,5] := remove (a 31) 2 [0,1,2,3,4,5] d31 b7
  have b8 : a 31 ≠ 5 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,3,4] := remove (a 31) 5 [0,1,3,4,5] t7 b8
  have b9 : a 31 ≠ 1 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 1 t4 c75 (by decide +kernel)
  have t9 : a 31 ∈ [0,3,4] := remove (a 31) 1 [0,1,3,4] t8 b9
  have b10 : a 31 ≠ 4 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 4 t4 c75 (by decide +kernel)
  have t10 : a 31 ∈ [0,3] := remove (a 31) 4 [0,3,4] t9 b10
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (t10))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_184
