import PartitionData205_207
namespace PartitionCover205_207
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,5,6,7,8,9,10,11])
    (d17 : a 17 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d22 : a 22 ∈ [0,1,2])
    (d23 : a 23 ∈ [0,1,2,3,5,7,9,11,13,15,17,19])
    (c52 : edge r52 (a 17) (a 19)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    : a 19 ∈ [0,6] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0,1,15,17,19] := by
  have b0 : a 19 ≠ 5 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 5 d17 c52 (by decide +kernel)
  have t0 : a 19 ∈ [0,1,6,7,8,9,10,11] := remove (a 19) 5 [0,1,5,6,7,8,9,10,11] d19 b0
  have b1 : a 19 ≠ 8 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 8 d17 c52 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,6,7,9,10,11] := remove (a 19) 8 [0,1,6,7,8,9,10,11] t0 b1
  have b2 : a 19 ≠ 9 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 9 d17 c52 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,6,7,10,11] := remove (a 19) 9 [0,1,6,7,9,10,11] t1 b2
  have b3 : a 19 ≠ 10 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 10 d17 c52 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,6,7,11] := remove (a 19) 10 [0,1,6,7,10,11] t2 b3
  have b4 : a 19 ≠ 11 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 11 d17 c52 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,6,7] := remove (a 19) 11 [0,1,6,7,11] t3 b4
  have b5 : a 19 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t5 : a 19 ∈ [0,6,7] := remove (a 19) 1 [0,1,6,7] t4 b5
  have b6 : a 19 ≠ 7 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t6 : a 19 ∈ [0,6] := remove (a 19) 7 [0,6,7] t5 b6
  have b7 : a 22 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t7 : a 22 ∈ [0,2] := remove (a 22) 1 [0,1,2] d22 b7
  have b8 : a 22 ≠ 2 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 2 d18 c56 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 2 [0,2] t7 b8
  have b9 : a 23 ≠ 2 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 2 t6 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,3,5,7,9,11,13,15,17,19] := remove (a 23) 2 [0,1,2,3,5,7,9,11,13,15,17,19] d23 b9
  have b10 : a 23 ≠ 3 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 3 t6 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,5,7,9,11,13,15,17,19] := remove (a 23) 3 [0,1,3,5,7,9,11,13,15,17,19] t9 b10
  have b11 : a 23 ≠ 5 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 5 t6 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,7,9,11,13,15,17,19] := remove (a 23) 5 [0,1,5,7,9,11,13,15,17,19] t10 b11
  have b12 : a 23 ≠ 7 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 7 t6 c58 (by decide +kernel)
  have t12 : a 23 ∈ [0,1,9,11,13,15,17,19] := remove (a 23) 7 [0,1,7,9,11,13,15,17,19] t11 b12
  have b13 : a 23 ≠ 9 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 9 t6 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,11,13,15,17,19] := remove (a 23) 9 [0,1,9,11,13,15,17,19] t12 b13
  have b14 : a 23 ≠ 11 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 11 t6 c58 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,13,15,17,19] := remove (a 23) 11 [0,1,11,13,15,17,19] t13 b14
  have b15 : a 23 ≠ 13 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 13 t6 c58 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,15,17,19] := remove (a 23) 13 [0,1,13,15,17,19] t14 b15
  exact And.intro t6 (And.intro t8 (t15))

theorem chunk9 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,15,17,19])
    (d19 : a 19 ∈ [0,6])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d20 : a 20 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,4,6,8,10])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d24 : a 24 ∈ [0,1])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 23 ∈ [0,1] ∧ a 21 ∈ [0,1] ∧ a 31 ∈ [0,1,2,3] ∧ a 25 ∈ [0,1,2,3,9,10,11] := by
  have b0 : a 23 ≠ 15 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 15 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,17,19] := remove (a 23) 15 [0,1,15,17,19] d23 b0
  have b1 : a 23 ≠ 17 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 17 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,19] := remove (a 23) 17 [0,1,17,19] t0 b1
  have b2 : a 23 ≠ 19 := exclude [0,6] (fun u v => edge r58 v u) (a 23) (a 19) 19 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,1] := remove (a 23) 19 [0,1,19] t1 b2
  have b3 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r60 v u) (a 21) (a 20) 2 d20 c60 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b3
  have b4 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r60 v u) (a 21) (a 20) 3 d20 c60 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] t3 b4
  have b5 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r60 v u) (a 21) (a 20) 4 d20 c60 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t4 b5
  have b6 : a 21 ≠ 5 := exclude [0,1] (fun u v => edge r60 v u) (a 21) (a 20) 5 d20 c60 (by decide +kernel)
  have t6 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t5 b6
  have b7 : a 31 ≠ 4 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 4 t2 c67 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,2,3,6,8,10] := remove (a 31) 4 [0,1,2,3,4,6,8,10] d31 b7
  have b8 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 6 t2 c67 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,2,3,8,10] := remove (a 31) 6 [0,1,2,3,6,8,10] t7 b8
  have b9 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 8 t2 c67 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,2,3,10] := remove (a 31) 8 [0,1,2,3,8,10] t8 b9
  have b10 : a 31 ≠ 10 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 10 t2 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,2,3] := remove (a 31) 10 [0,1,2,3,10] t9 b10
  have b11 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 25) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b11
  have b12 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 5 d24 c68 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 25) 5 [0,1,2,3,5,6,7,8,9,10,11] t11 b12
  have b13 : a 25 ≠ 6 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 6 d24 c68 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 25) 6 [0,1,2,3,6,7,8,9,10,11] t12 b13
  have b14 : a 25 ≠ 7 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 7 d24 c68 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,2,3,8,9,10,11] := remove (a 25) 7 [0,1,2,3,7,8,9,10,11] t13 b14
  have b15 : a 25 ≠ 8 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 8 d24 c68 (by decide +kernel)
  have t15 : a 25 ∈ [0,1,2,3,9,10,11] := remove (a 25) 8 [0,1,2,3,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t10 (t15)))

theorem chunk10 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,9,10,11])
    (d24 : a 24 ∈ [0,1])
    (d28 : a 28 ∈ [0,1,4,8])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d30 : a 30 ∈ [0,1,2,3])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 25 ∈ [0,1,2,3] ∧ a 24 ∈ [0] ∧ a 28 ∈ [0,1] ∧ a 27 ∈ [0,1,2,3] ∧ a 30 ∈ [0,1] := by
  have b0 : a 25 ≠ 9 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 9 d24 c68 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,2,3,10,11] := remove (a 25) 9 [0,1,2,3,9,10,11] d25 b0
  have b1 : a 25 ≠ 10 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 10 d24 c68 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,2,3,11] := remove (a 25) 10 [0,1,2,3,10,11] t0 b1
  have b2 : a 25 ≠ 11 := exclude [0,1] (fun u v => edge r68 v u) (a 25) (a 24) 11 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,2,3] := remove (a 25) 11 [0,1,2,3,11] t1 b2
  have b3 : a 24 ≠ 1 := exclude [0,1,4,8] (edge r70) (a 24) (a 28) 1 d28 c70 (by decide +kernel)
  have t3 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b3
  have b4 : a 28 ≠ 4 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 4 t3 c70 (by decide +kernel)
  have t4 : a 28 ∈ [0,1,8] := remove (a 28) 4 [0,1,4,8] d28 b4
  have b5 : a 28 ≠ 8 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 8 t3 c70 (by decide +kernel)
  have t5 : a 28 ∈ [0,1] := remove (a 28) 8 [0,1,8] t4 b5
  have b6 : a 27 ≠ 4 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 4 t2 c71 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b6
  have b7 : a 27 ≠ 5 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 5 t2 c71 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 27) 5 [0,1,2,3,5,6,7,8,9,10,11] t6 b7
  have b8 : a 27 ≠ 6 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 6 t2 c71 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,2,3,7,8,9,10,11] := remove (a 27) 6 [0,1,2,3,6,7,8,9,10,11] t7 b8
  have b9 : a 27 ≠ 7 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 7 t2 c71 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,2,3,8,9,10,11] := remove (a 27) 7 [0,1,2,3,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 8 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 8 t2 c71 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,2,3,9,10,11] := remove (a 27) 8 [0,1,2,3,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 9 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 9 t2 c71 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,2,3,10,11] := remove (a 27) 9 [0,1,2,3,9,10,11] t10 b11
  have b12 : a 27 ≠ 10 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 10 t2 c71 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,2,3,11] := remove (a 27) 10 [0,1,2,3,10,11] t11 b12
  have b13 : a 27 ≠ 11 := exclude [0,1,2,3] (fun u v => edge r71 v u) (a 27) (a 25) 11 t2 c71 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,2,3] := remove (a 27) 11 [0,1,2,3,11] t12 b13
  have b14 : a 30 ≠ 2 := exclude [0,1] (fun u v => edge r77 v u) (a 30) (a 28) 2 t5 c77 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,3] := remove (a 30) 2 [0,1,2,3] d30 b14
  have b15 : a 30 ≠ 3 := exclude [0,1] (fun u v => edge r77 v u) (a 30) (a 28) 3 t5 c77 (by decide +kernel)
  have t15 : a 30 ∈ [0,1] := remove (a 30) 3 [0,1,3] t14 b15
  exact And.intro t2 (And.intro t3 (And.intro t5 (And.intro t13 (t15))))

theorem chunk11 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,2])
    (d13 : a 13 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1,2,3])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 5 ∈ [0] ∧ a 25 ∈ [0,2] ∧ a 27 ∈ [0,2] ∧ a 31 ∈ [0,1] := by
  have b0 : a 5 ≠ 1 := exclude [0,1] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t0 : a 5 ∈ [0,2] := remove (a 5) 1 [0,1,2] d5 b0
  have b1 : a 5 ≠ 2 := exclude [0,1] (edge r21) (a 5) (a 13) 2 d13 c21 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 2 [0,2] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b2
  have b3 : a 25 ≠ 3 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 3 d24 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t2 b3
  have b4 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r71 v u) (a 27) (a 25) 1 t3 c71 (by decide +kernel)
  have t4 : a 27 ∈ [0,2,3] := remove (a 27) 1 [0,1,2,3] d27 b4
  have b5 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r71 v u) (a 27) (a 25) 3 t3 c71 (by decide +kernel)
  have t5 : a 27 ∈ [0,2] := remove (a 27) 3 [0,2,3] t4 b5
  have b6 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 2 t5 c75 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b6
  have b7 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 3 t5 c75 (by decide +kernel)
  have t7 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t6 b7
  exact And.intro t1 (And.intro t3 (And.intro t5 (t7)))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_207
