import PartitionData205_203
namespace PartitionCover205_203
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,4,5])
    (d11 : a 11 ∈ [0,6])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0,6])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1])
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 15 ∈ [0,4] ∧ a 27 ∈ [0,1,4,7] ∧ a 28 ∈ [0,2,5] ∧ a 29 ∈ [0,1,2,4,5] := by
  have b0 : a 15 ≠ 5 := exclude [0,6] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [0,4] := remove (a 15) 5 [0,4,5] d15 b0
  have b1 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,3,4,5,6,7,8] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8] d27 b1
  have b2 : a 27 ≠ 3 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,4,5,6,7,8] := remove (a 27) 3 [0,1,3,4,5,6,7,8] t1 b2
  have b3 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,4,6,7,8] := remove (a 27) 5 [0,1,4,5,6,7,8] t2 b3
  have b4 : a 27 ≠ 6 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,4,7,8] := remove (a 27) 6 [0,1,4,6,7,8] t3 b4
  have b5 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,4,7] := remove (a 27) 8 [0,1,4,7,8] t4 b5
  have b6 : a 28 ≠ 1 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b6
  have b7 : a 28 ≠ 3 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 28) 3 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 28 ≠ 4 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 28) 4 [0,2,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 28 ≠ 6 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,2,5,7,8,9,10,11] := remove (a 28) 6 [0,2,5,6,7,8,9,10,11] t8 b9
  have b10 : a 28 ≠ 7 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,5,8,9,10,11] := remove (a 28) 7 [0,2,5,7,8,9,10,11] t9 b10
  have b11 : a 28 ≠ 8 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,5,9,10,11] := remove (a 28) 8 [0,2,5,8,9,10,11] t10 b11
  have b12 : a 28 ≠ 9 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,5,10,11] := remove (a 28) 9 [0,2,5,9,10,11] t11 b12
  have b13 : a 28 ≠ 10 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,2,5,11] := remove (a 28) 10 [0,2,5,10,11] t12 b13
  have b14 : a 28 ≠ 11 := exclude [0,6] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,5] := remove (a 28) 11 [0,2,5,11] t13 b14
  have b15 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,2,4,5] := remove (a 29) 3 [0,1,2,3,4,5] d29 b15
  exact And.intro t0 (And.intro t5 (And.intro t14 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,2,4,5])
    (d13 : a 13 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2])
    (d15 : a 15 ∈ [0,4])
    (d17 : a 17 ∈ [0,1,2])
    (d16 : a 16 ∈ [0,2])
    (d20 : a 20 ∈ [0,1,2])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 29 ∈ [0,1,2,4] ∧ a 30 ∈ [0,1] ∧ a 31 ∈ [0] ∧ a 17 ∈ [0,1] ∧ a 20 ∈ [0,1] ∧ a 21 ∈ [0,1,3,4,5] := by
  have b0 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,2,4] := remove (a 29) 5 [0,1,2,4,5] d29 b0
  have b1 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b1
  have b2 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 30) 4 [0,1,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,6,7,8,9,10,11] := remove (a 30) 5 [0,1,5,6,7,8,9,10,11] t3 b4
  have b5 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,7,8,9,10,11] := remove (a 30) 6 [0,1,6,7,8,9,10,11] t4 b5
  have b6 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,8,9,10,11] := remove (a 30) 7 [0,1,7,8,9,10,11] t5 b6
  have b7 : a 30 ≠ 8 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,9,10,11] := remove (a 30) 8 [0,1,8,9,10,11] t6 b7
  have b8 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,10,11] := remove (a 30) 9 [0,1,9,10,11] t7 b8
  have b9 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,11] := remove (a 30) 10 [0,1,10,11] t8 b9
  have b10 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1] := remove (a 30) 11 [0,1,11] t9 b10
  have b11 : a 31 ≠ 1 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,2] := remove (a 31) 1 [0,1,2] d31 b11
  have b12 : a 31 ≠ 2 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0] := remove (a 31) 2 [0,2] t11 b12
  have b13 : a 17 ≠ 2 := exclude [0,2] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0,1] := remove (a 17) 2 [0,1,2] d17 b13
  have b14 : a 20 ≠ 2 := exclude [0,2] (fun u v => edge r50 v u) (a 20) (a 16) 2 d16 c50 (by decide +kernel)
  have t14 : a 20 ∈ [0,1] := remove (a 20) 2 [0,1,2] d20 b14
  have b15 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 2 t13 c53 (by decide +kernel)
  have t15 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b15
  exact And.intro t0 (And.intro t10 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))

theorem chunk10 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,3,4,5])
    (d17 : a 17 ∈ [0,1])
    (d25 : a 25 ∈ [0,2,4,5,6,7,8])
    (d18 : a 18 ∈ [0,3])
    (d19 : a 19 ∈ [0,4,6,8])
    (d22 : a 22 ∈ [0,1,6])
    (d23 : a 23 ∈ [0,1,3,4])
    (d29 : a 29 ∈ [0,1,2,4])
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    : a 21 ∈ [0,1] ∧ a 25 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0,6] ∧ a 22 ∈ [0,6] ∧ a 23 ∈ [0,3] ∧ a 29 ∈ [0,1] := by
  have b0 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 3 d17 c53 (by decide +kernel)
  have t0 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] d21 b0
  have b1 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t0 b1
  have b2 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t2 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t1 b2
  have b3 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 4 d17 c54 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,5,6,7,8] := remove (a 25) 4 [0,2,4,5,6,7,8] d25 b3
  have b4 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 5 d17 c54 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,6,7,8] := remove (a 25) 5 [0,2,5,6,7,8] t3 b4
  have b5 : a 25 ≠ 6 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 6 d17 c54 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,7,8] := remove (a 25) 6 [0,2,6,7,8] t4 b5
  have b6 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 7 d17 c54 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,8] := remove (a 25) 7 [0,2,7,8] t5 b6
  have b7 : a 25 ≠ 8 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 8 d17 c54 (by decide +kernel)
  have t7 : a 25 ∈ [0,2] := remove (a 25) 8 [0,2,8] t6 b7
  have b8 : a 18 ≠ 3 := exclude [0,4,6,8] (edge r55) (a 18) (a 19) 3 d19 c55 (by decide +kernel)
  have t8 : a 18 ∈ [0] := remove (a 18) 3 [0,3] d18 b8
  have b9 : a 19 ≠ 4 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 4 t8 c55 (by decide +kernel)
  have t9 : a 19 ∈ [0,6,8] := remove (a 19) 4 [0,4,6,8] d19 b9
  have b10 : a 19 ≠ 8 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 8 t8 c55 (by decide +kernel)
  have t10 : a 19 ∈ [0,6] := remove (a 19) 8 [0,6,8] t9 b10
  have b11 : a 22 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 1 t8 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,6] := remove (a 22) 1 [0,1,6] d22 b11
  have b12 : a 23 ≠ 1 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 1 t10 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,3,4] := remove (a 23) 1 [0,1,3,4] d23 b12
  have b13 : a 23 ≠ 4 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 4 t10 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,3] := remove (a 23) 4 [0,3,4] t12 b13
  have b14 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r64 v u) (a 29) (a 21) 2 t2 c64 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,4] := remove (a 29) 2 [0,1,2,4] d29 b14
  have b15 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r64 v u) (a 29) (a 21) 4 t2 c64 (by decide +kernel)
  have t15 : a 29 ∈ [0,1] := remove (a 29) 4 [0,1,4] t14 b15
  exact And.intro t2 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t13 (t15))))))

theorem chunk11 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,9])
    (d25 : a 25 ∈ [0,2])
    (d28 : a 28 ∈ [0,2,5])
    (d27 : a 27 ∈ [0,1,4,7])
    (d26 : a 26 ∈ [0,2])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 24 ∈ [0] ∧ a 28 ∈ [0] ∧ a 27 ∈ [0,1] := by
  have b0 : a 24 ≠ 9 := exclude [0,2] (edge r68) (a 24) (a 25) 9 d25 c68 (by decide +kernel)
  have t0 : a 24 ∈ [0] := remove (a 24) 9 [0,9] d24 b0
  have b1 : a 28 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 2 t0 c70 (by decide +kernel)
  have t1 : a 28 ∈ [0,5] := remove (a 28) 2 [0,2,5] d28 b1
  have b2 : a 28 ≠ 5 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 5 t0 c70 (by decide +kernel)
  have t2 : a 28 ∈ [0] := remove (a 28) 5 [0,5] t1 b2
  have b3 : a 27 ≠ 4 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 4 d26 c73 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,7] := remove (a 27) 4 [0,1,4,7] d27 b3
  have b4 : a 27 ≠ 7 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 7 d26 c73 (by decide +kernel)
  have t4 : a 27 ∈ [0,1] := remove (a 27) 7 [0,1,7] t3 b4
  exact And.intro t0 (And.intro t2 (t4))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_203
