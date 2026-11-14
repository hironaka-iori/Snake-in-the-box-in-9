import PartitionData205_175
namespace PartitionCover205_175
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,3,12,13,14,15,16,17,18,19])
    (d14 : a 14 ∈ [0,3])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,13])
    (d16 : a 16 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,2])
    (d20 : a 20 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 30 ∈ [0,1,2,3] ∧ a 31 ∈ [0,2,3,5] ∧ a 16 ∈ [0,2] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0] ∧ a 23 ∈ [0,1] := by
  have b0 : a 30 ≠ 12 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,2,3,13,14,15,16,17,18,19] := remove (a 30) 12 [0,1,2,3,12,13,14,15,16,17,18,19] d30 b0
  have b1 : a 30 ≠ 13 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,2,3,14,15,16,17,18,19] := remove (a 30) 13 [0,1,2,3,13,14,15,16,17,18,19] t0 b1
  have b2 : a 30 ≠ 14 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,2,3,15,16,17,18,19] := remove (a 30) 14 [0,1,2,3,14,15,16,17,18,19] t1 b2
  have b3 : a 30 ≠ 15 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,2,3,16,17,18,19] := remove (a 30) 15 [0,1,2,3,15,16,17,18,19] t2 b3
  have b4 : a 30 ≠ 16 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,2,3,17,18,19] := remove (a 30) 16 [0,1,2,3,16,17,18,19] t3 b4
  have b5 : a 30 ≠ 17 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,2,3,18,19] := remove (a 30) 17 [0,1,2,3,17,18,19] t4 b5
  have b6 : a 30 ≠ 18 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 18 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,2,3,19] := remove (a 30) 18 [0,1,2,3,18,19] t5 b6
  have b7 : a 30 ≠ 19 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 19 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,2,3] := remove (a 30) 19 [0,1,2,3,19] t6 b7
  have b8 : a 31 ≠ 1 := exclude [0,13] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,2,3,4,5] := remove (a 31) 1 [0,1,2,3,4,5] d31 b8
  have b9 : a 31 ≠ 4 := exclude [0,13] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,2,3,5] := remove (a 31) 4 [0,2,3,4,5] t8 b9
  have b10 : a 16 ≠ 1 := exclude [0,2] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t10 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b10
  have b11 : a 16 ≠ 3 := exclude [0,2] (edge r49) (a 16) (a 18) 3 d18 c49 (by decide +kernel)
  have t11 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t10 b11
  have b12 : a 20 ≠ 1 := exclude [0,2] (fun u v => edge r50 v u) (a 20) (a 16) 1 t11 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b12
  have b13 : a 21 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 1 t12 c60 (by decide +kernel)
  have t13 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b13
  have b14 : a 23 ≠ 2 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 2 t13 c63 (by decide +kernel)
  have t14 : a 23 ∈ [0,1,3] := remove (a 23) 2 [0,1,2,3] d23 b14
  have b15 : a 23 ≠ 3 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 3 t13 c63 (by decide +kernel)
  have t15 : a 23 ∈ [0,1] := remove (a 23) 3 [0,1,3] t14 b15
  exact And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t13 (t15)))))

theorem chunk9 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,2,3,5])
    (d23 : a 23 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,5,7,9,11,13,15,17,19])
    (d25 : a 25 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9])
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    : a 31 ∈ [0,3] ∧ a 24 ∈ [0,1] ∧ a 26 ∈ [0,5,6,7,8,9] := by
  have b0 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,3,5] := remove (a 31) 2 [0,2,3,5] d31 b0
  have b1 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0,3] := remove (a 31) 5 [0,3,5] t0 b1
  have b2 : a 24 ≠ 2 := exclude [0] (edge r68) (a 24) (a 25) 2 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,3,5,7,9,11,13,15,17,19] := remove (a 24) 2 [0,1,2,3,5,7,9,11,13,15,17,19] d24 b2
  have b3 : a 24 ≠ 3 := exclude [0] (edge r68) (a 24) (a 25) 3 d25 c68 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,5,7,9,11,13,15,17,19] := remove (a 24) 3 [0,1,3,5,7,9,11,13,15,17,19] t2 b3
  have b4 : a 24 ≠ 5 := exclude [0] (edge r68) (a 24) (a 25) 5 d25 c68 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,7,9,11,13,15,17,19] := remove (a 24) 5 [0,1,5,7,9,11,13,15,17,19] t3 b4
  have b5 : a 24 ≠ 7 := exclude [0] (edge r68) (a 24) (a 25) 7 d25 c68 (by decide +kernel)
  have t5 : a 24 ∈ [0,1,9,11,13,15,17,19] := remove (a 24) 7 [0,1,7,9,11,13,15,17,19] t4 b5
  have b6 : a 24 ≠ 9 := exclude [0] (edge r68) (a 24) (a 25) 9 d25 c68 (by decide +kernel)
  have t6 : a 24 ∈ [0,1,11,13,15,17,19] := remove (a 24) 9 [0,1,9,11,13,15,17,19] t5 b6
  have b7 : a 24 ≠ 11 := exclude [0] (edge r68) (a 24) (a 25) 11 d25 c68 (by decide +kernel)
  have t7 : a 24 ∈ [0,1,13,15,17,19] := remove (a 24) 11 [0,1,11,13,15,17,19] t6 b7
  have b8 : a 24 ≠ 13 := exclude [0] (edge r68) (a 24) (a 25) 13 d25 c68 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,15,17,19] := remove (a 24) 13 [0,1,13,15,17,19] t7 b8
  have b9 : a 24 ≠ 15 := exclude [0] (edge r68) (a 24) (a 25) 15 d25 c68 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,17,19] := remove (a 24) 15 [0,1,15,17,19] t8 b9
  have b10 : a 24 ≠ 17 := exclude [0] (edge r68) (a 24) (a 25) 17 d25 c68 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,19] := remove (a 24) 17 [0,1,17,19] t9 b10
  have b11 : a 24 ≠ 19 := exclude [0] (edge r68) (a 24) (a 25) 19 d25 c68 (by decide +kernel)
  have t11 : a 24 ∈ [0,1] := remove (a 24) 19 [0,1,19] t10 b11
  have b12 : a 26 ≠ 1 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 1 t11 c69 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9] d26 b12
  have b13 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 2 t11 c69 (by decide +kernel)
  have t13 : a 26 ∈ [0,3,4,5,6,7,8,9] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9] t12 b13
  have b14 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 3 t11 c69 (by decide +kernel)
  have t14 : a 26 ∈ [0,4,5,6,7,8,9] := remove (a 26) 3 [0,3,4,5,6,7,8,9] t13 b14
  have b15 : a 26 ≠ 4 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 4 t11 c69 (by decide +kernel)
  have t15 : a 26 ∈ [0,5,6,7,8,9] := remove (a 26) 4 [0,4,5,6,7,8,9] t14 b15
  exact And.intro t1 (And.intro t11 (t15))

theorem chunk10 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,5,6,7,8,9])
    (d24 : a 24 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,3,4])
    (d25 : a 25 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c69 : edge r69 (a 24) (a 26)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 26 ∈ [0] ∧ a 27 ∈ [0,3] ∧ a 29 ∈ [0,6,11] := by
  have b0 : a 26 ≠ 5 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 5 d24 c69 (by decide +kernel)
  have t0 : a 26 ∈ [0,6,7,8,9] := remove (a 26) 5 [0,5,6,7,8,9] d26 b0
  have b1 : a 26 ≠ 6 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 6 d24 c69 (by decide +kernel)
  have t1 : a 26 ∈ [0,7,8,9] := remove (a 26) 6 [0,6,7,8,9] t0 b1
  have b2 : a 26 ≠ 7 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 7 d24 c69 (by decide +kernel)
  have t2 : a 26 ∈ [0,8,9] := remove (a 26) 7 [0,7,8,9] t1 b2
  have b3 : a 26 ≠ 8 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 8 d24 c69 (by decide +kernel)
  have t3 : a 26 ∈ [0,9] := remove (a 26) 8 [0,8,9] t2 b3
  have b4 : a 26 ≠ 9 := exclude [0,1] (fun u v => edge r69 v u) (a 26) (a 24) 9 d24 c69 (by decide +kernel)
  have t4 : a 26 ∈ [0] := remove (a 26) 9 [0,9] t3 b4
  have b5 : a 27 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 1 d25 c71 (by decide +kernel)
  have t5 : a 27 ∈ [0,3,4] := remove (a 27) 1 [0,1,3,4] d27 b5
  have b6 : a 27 ≠ 4 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 4 d25 c71 (by decide +kernel)
  have t6 : a 27 ∈ [0,3] := remove (a 27) 4 [0,3,4] t5 b6
  have b7 : a 29 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 1 d25 c72 (by decide +kernel)
  have t7 : a 29 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 29) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b7
  have b8 : a 29 ≠ 2 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 2 d25 c72 (by decide +kernel)
  have t8 : a 29 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 29) 2 [0,2,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 29 ≠ 3 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 3 d25 c72 (by decide +kernel)
  have t9 : a 29 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 29) 3 [0,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 29 ≠ 4 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 4 d25 c72 (by decide +kernel)
  have t10 : a 29 ∈ [0,5,6,7,8,9,10,11] := remove (a 29) 4 [0,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 29 ≠ 5 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 5 d25 c72 (by decide +kernel)
  have t11 : a 29 ∈ [0,6,7,8,9,10,11] := remove (a 29) 5 [0,5,6,7,8,9,10,11] t10 b11
  have b12 : a 29 ≠ 7 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 7 d25 c72 (by decide +kernel)
  have t12 : a 29 ∈ [0,6,8,9,10,11] := remove (a 29) 7 [0,6,7,8,9,10,11] t11 b12
  have b13 : a 29 ≠ 8 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 8 d25 c72 (by decide +kernel)
  have t13 : a 29 ∈ [0,6,9,10,11] := remove (a 29) 8 [0,6,8,9,10,11] t12 b13
  have b14 : a 29 ≠ 9 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 9 d25 c72 (by decide +kernel)
  have t14 : a 29 ∈ [0,6,10,11] := remove (a 29) 9 [0,6,9,10,11] t13 b14
  have b15 : a 29 ≠ 10 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 10 d25 c72 (by decide +kernel)
  have t15 : a 29 ∈ [0,6,11] := remove (a 29) 10 [0,6,10,11] t14 b15
  exact And.intro t4 (And.intro t6 (t15))

theorem chunk11 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,6,11])
    (d25 : a 25 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0])
    (d11 : a 11 ∈ [0,2,6,8])
    (d15 : a 15 ∈ [0,13])
    (d12 : a 12 ∈ [0,1,10,11])
    (d13 : a 13 ∈ [0])
    (c38 : edge r38 (a 11) (a 15)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 29 ∈ [0,6] ∧ a 30 ∈ [0,1] ∧ a 11 ∈ [0,6] ∧ a 12 ∈ [0,1] := by
  have b0 : a 29 ≠ 11 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 11 d25 c72 (by decide +kernel)
  have t0 : a 29 ∈ [0,6] := remove (a 29) 11 [0,6,11] d29 b0
  have b1 : a 30 ≠ 2 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 2 d26 c74 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,3] := remove (a 30) 2 [0,1,2,3] d30 b1
  have b2 : a 30 ≠ 3 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 3 d26 c74 (by decide +kernel)
  have t2 : a 30 ∈ [0,1] := remove (a 30) 3 [0,1,3] t1 b2
  have b3 : a 11 ≠ 2 := exclude [0,13] (edge r38) (a 11) (a 15) 2 d15 c38 (by decide +kernel)
  have t3 : a 11 ∈ [0,6,8] := remove (a 11) 2 [0,2,6,8] d11 b3
  have b4 : a 11 ≠ 8 := exclude [0,13] (edge r38) (a 11) (a 15) 8 d15 c38 (by decide +kernel)
  have t4 : a 11 ∈ [0,6] := remove (a 11) 8 [0,6,8] t3 b4
  have b5 : a 12 ≠ 10 := exclude [0] (edge r40) (a 12) (a 13) 10 d13 c40 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,11] := remove (a 12) 10 [0,1,10,11] d12 b5
  have b6 : a 12 ≠ 11 := exclude [0] (edge r40) (a 12) (a 13) 11 d13 c40 (by decide +kernel)
  have t6 : a 12 ∈ [0,1] := remove (a 12) 11 [0,1,11] t5 b6
  exact And.intro t0 (And.intro t2 (And.intro t4 (t6)))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_175
