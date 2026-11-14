import PartitionData205_189
namespace PartitionCover205_189
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,11,18])
    (d14 : a 14 ∈ [0,1,2,3,4,5,18,19,20,21,22,23])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c35 : edge r35 (a 10) (a 14)=true)
    (c36 : edge r36 (a 10) (a 25)=true)
    : a 10 ∈ [0,18] ∧ a 14 ∈ [0,18] ∧ a 25 ∈ [0,4,7,8,9,10,11] := by
  have b0 : a 10 ≠ 11 := exclude [0,1,2,3,4,5,18,19,20,21,22,23] (edge r35) (a 10) (a 14) 11 d14 c35 (by decide +kernel)
  have t0 : a 10 ∈ [0,18] := remove (a 10) 11 [0,11,18] d10 b0
  have b1 : a 14 ≠ 1 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 1 t0 c35 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,3,4,5,18,19,20,21,22,23] := remove (a 14) 1 [0,1,2,3,4,5,18,19,20,21,22,23] d14 b1
  have b2 : a 14 ≠ 2 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 2 t0 c35 (by decide +kernel)
  have t2 : a 14 ∈ [0,3,4,5,18,19,20,21,22,23] := remove (a 14) 2 [0,2,3,4,5,18,19,20,21,22,23] t1 b2
  have b3 : a 14 ≠ 3 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 3 t0 c35 (by decide +kernel)
  have t3 : a 14 ∈ [0,4,5,18,19,20,21,22,23] := remove (a 14) 3 [0,3,4,5,18,19,20,21,22,23] t2 b3
  have b4 : a 14 ≠ 4 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 4 t0 c35 (by decide +kernel)
  have t4 : a 14 ∈ [0,5,18,19,20,21,22,23] := remove (a 14) 4 [0,4,5,18,19,20,21,22,23] t3 b4
  have b5 : a 14 ≠ 5 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 5 t0 c35 (by decide +kernel)
  have t5 : a 14 ∈ [0,18,19,20,21,22,23] := remove (a 14) 5 [0,5,18,19,20,21,22,23] t4 b5
  have b6 : a 14 ≠ 19 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 19 t0 c35 (by decide +kernel)
  have t6 : a 14 ∈ [0,18,20,21,22,23] := remove (a 14) 19 [0,18,19,20,21,22,23] t5 b6
  have b7 : a 14 ≠ 20 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 20 t0 c35 (by decide +kernel)
  have t7 : a 14 ∈ [0,18,21,22,23] := remove (a 14) 20 [0,18,20,21,22,23] t6 b7
  have b8 : a 14 ≠ 21 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 21 t0 c35 (by decide +kernel)
  have t8 : a 14 ∈ [0,18,22,23] := remove (a 14) 21 [0,18,21,22,23] t7 b8
  have b9 : a 14 ≠ 22 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 22 t0 c35 (by decide +kernel)
  have t9 : a 14 ∈ [0,18,23] := remove (a 14) 22 [0,18,22,23] t8 b9
  have b10 : a 14 ≠ 23 := exclude [0,18] (fun u v => edge r35 v u) (a 14) (a 10) 23 t0 c35 (by decide +kernel)
  have t10 : a 14 ∈ [0,18] := remove (a 14) 23 [0,18,23] t9 b10
  have b11 : a 25 ≠ 1 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 1 t0 c36 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b11
  have b12 : a 25 ≠ 2 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 2 t0 c36 (by decide +kernel)
  have t12 : a 25 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 25 ≠ 3 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 3 t0 c36 (by decide +kernel)
  have t13 : a 25 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 25 ≠ 5 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 5 t0 c36 (by decide +kernel)
  have t14 : a 25 ∈ [0,4,6,7,8,9,10,11] := remove (a 25) 5 [0,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 25 ≠ 6 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 6 t0 c36 (by decide +kernel)
  have t15 : a 25 ∈ [0,4,7,8,9,10,11] := remove (a 25) 6 [0,4,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t10 (t15))

theorem chunk9 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,4,7,8,9,10,11])
    (d10 : a 10 ∈ [0,18])
    (d15 : a 15 ∈ [0,1,3,4,6,7])
    (d11 : a 11 ∈ [0,19])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,2])
    (c36 : edge r36 (a 10) (a 25)=true)
    (c37 : edge r37 (a 11) (a 15)=true)
    (c38 : edge r38 (a 11) (a 26)=true)
    (c41 : edge r41 (a 12) (a 27)=true)
    : a 25 ∈ [0,4,8,10] ∧ a 15 ∈ [0,1,3,6] ∧ a 26 ∈ [0,4] ∧ a 27 ∈ [0,2,3,4,5] := by
  have b0 : a 25 ≠ 7 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 7 d10 c36 (by decide +kernel)
  have t0 : a 25 ∈ [0,4,8,9,10,11] := remove (a 25) 7 [0,4,7,8,9,10,11] d25 b0
  have b1 : a 25 ≠ 9 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 9 d10 c36 (by decide +kernel)
  have t1 : a 25 ∈ [0,4,8,10,11] := remove (a 25) 9 [0,4,8,9,10,11] t0 b1
  have b2 : a 25 ≠ 11 := exclude [0,18] (fun u v => edge r36 v u) (a 25) (a 10) 11 d10 c36 (by decide +kernel)
  have t2 : a 25 ∈ [0,4,8,10] := remove (a 25) 11 [0,4,8,10,11] t1 b2
  have b3 : a 15 ≠ 4 := exclude [0,19] (fun u v => edge r37 v u) (a 15) (a 11) 4 d11 c37 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,3,6,7] := remove (a 15) 4 [0,1,3,4,6,7] d15 b3
  have b4 : a 15 ≠ 7 := exclude [0,19] (fun u v => edge r37 v u) (a 15) (a 11) 7 d11 c37 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,3,6] := remove (a 15) 7 [0,1,3,6,7] t3 b4
  have b5 : a 26 ≠ 1 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 1 d11 c38 (by decide +kernel)
  have t5 : a 26 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 26) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d26 b5
  have b6 : a 26 ≠ 2 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 2 d11 c38 (by decide +kernel)
  have t6 : a 26 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 26) 2 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 26 ≠ 3 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 3 d11 c38 (by decide +kernel)
  have t7 : a 26 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 26) 3 [0,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 26 ≠ 5 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 5 d11 c38 (by decide +kernel)
  have t8 : a 26 ∈ [0,4,6,7,8,9,10,11] := remove (a 26) 5 [0,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 26 ≠ 6 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 6 d11 c38 (by decide +kernel)
  have t9 : a 26 ∈ [0,4,7,8,9,10,11] := remove (a 26) 6 [0,4,6,7,8,9,10,11] t8 b9
  have b10 : a 26 ≠ 7 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 7 d11 c38 (by decide +kernel)
  have t10 : a 26 ∈ [0,4,8,9,10,11] := remove (a 26) 7 [0,4,7,8,9,10,11] t9 b10
  have b11 : a 26 ≠ 8 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 8 d11 c38 (by decide +kernel)
  have t11 : a 26 ∈ [0,4,9,10,11] := remove (a 26) 8 [0,4,8,9,10,11] t10 b11
  have b12 : a 26 ≠ 9 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 9 d11 c38 (by decide +kernel)
  have t12 : a 26 ∈ [0,4,10,11] := remove (a 26) 9 [0,4,9,10,11] t11 b12
  have b13 : a 26 ≠ 10 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 10 d11 c38 (by decide +kernel)
  have t13 : a 26 ∈ [0,4,11] := remove (a 26) 10 [0,4,10,11] t12 b13
  have b14 : a 26 ≠ 11 := exclude [0,19] (fun u v => edge r38 v u) (a 26) (a 11) 11 d11 c38 (by decide +kernel)
  have t14 : a 26 ∈ [0,4] := remove (a 26) 11 [0,4,11] t13 b14
  have b15 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r41 v u) (a 27) (a 12) 1 d12 c41 (by decide +kernel)
  have t15 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b15
  exact And.intro t2 (And.intro t4 (And.intro t14 (t15)))

theorem chunk10 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2,3,4,5])
    (d12 : a 12 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1,3,6])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c41 : edge r41 (a 12) (a 27)=true)
    (c42 : edge r42 (a 13) (a 15)=true)
    (c43 : edge r43 (a 13) (a 28)=true)
    : a 27 ∈ [0,2] ∧ a 13 ∈ [0,1,3,4] ∧ a 15 ∈ [0,1] ∧ a 28 ∈ [0,1,2,3,6,7,8,9,17] := by
  have b0 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r41 v u) (a 27) (a 12) 3 d12 c41 (by decide +kernel)
  have t0 : a 27 ∈ [0,2,4,5] := remove (a 27) 3 [0,2,3,4,5] d27 b0
  have b1 : a 27 ≠ 4 := exclude [0,2] (fun u v => edge r41 v u) (a 27) (a 12) 4 d12 c41 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,5] := remove (a 27) 4 [0,2,4,5] t0 b1
  have b2 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r41 v u) (a 27) (a 12) 5 d12 c41 (by decide +kernel)
  have t2 : a 27 ∈ [0,2] := remove (a 27) 5 [0,2,5] t1 b2
  have b3 : a 13 ≠ 2 := exclude [0,1,3,6] (edge r42) (a 13) (a 15) 2 d15 c42 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b3
  have b4 : a 13 ≠ 5 := exclude [0,1,3,6] (edge r42) (a 13) (a 15) 5 d15 c42 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,3,4] := remove (a 13) 5 [0,1,3,4,5] t3 b4
  have b5 : a 15 ≠ 3 := exclude [0,1,3,4] (fun u v => edge r42 v u) (a 15) (a 13) 3 t4 c42 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,6] := remove (a 15) 3 [0,1,3,6] d15 b5
  have b6 : a 15 ≠ 6 := exclude [0,1,3,4] (fun u v => edge r42 v u) (a 15) (a 13) 6 t4 c42 (by decide +kernel)
  have t6 : a 15 ∈ [0,1] := remove (a 15) 6 [0,1,6] t5 b6
  have b7 : a 28 ≠ 4 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 4 t4 c43 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d28 b7
  have b8 : a 28 ≠ 5 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 5 t4 c43 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 28) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 28 ≠ 10 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 10 t4 c43 (by decide +kernel)
  have t9 : a 28 ∈ [0,1,2,3,6,7,8,9,11,12,13,14,15,16,17] := remove (a 28) 10 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 28 ≠ 11 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 11 t4 c43 (by decide +kernel)
  have t10 : a 28 ∈ [0,1,2,3,6,7,8,9,12,13,14,15,16,17] := remove (a 28) 11 [0,1,2,3,6,7,8,9,11,12,13,14,15,16,17] t9 b10
  have b11 : a 28 ≠ 12 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 12 t4 c43 (by decide +kernel)
  have t11 : a 28 ∈ [0,1,2,3,6,7,8,9,13,14,15,16,17] := remove (a 28) 12 [0,1,2,3,6,7,8,9,12,13,14,15,16,17] t10 b11
  have b12 : a 28 ≠ 13 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 13 t4 c43 (by decide +kernel)
  have t12 : a 28 ∈ [0,1,2,3,6,7,8,9,14,15,16,17] := remove (a 28) 13 [0,1,2,3,6,7,8,9,13,14,15,16,17] t11 b12
  have b13 : a 28 ≠ 14 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 14 t4 c43 (by decide +kernel)
  have t13 : a 28 ∈ [0,1,2,3,6,7,8,9,15,16,17] := remove (a 28) 14 [0,1,2,3,6,7,8,9,14,15,16,17] t12 b13
  have b14 : a 28 ≠ 15 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 15 t4 c43 (by decide +kernel)
  have t14 : a 28 ∈ [0,1,2,3,6,7,8,9,16,17] := remove (a 28) 15 [0,1,2,3,6,7,8,9,15,16,17] t13 b14
  have b15 : a 28 ≠ 16 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 16 t4 c43 (by decide +kernel)
  have t15 : a 28 ∈ [0,1,2,3,6,7,8,9,17] := remove (a 28) 16 [0,1,2,3,6,7,8,9,16,17] t14 b15
  exact And.intro t2 (And.intro t4 (And.intro t6 (t15)))

theorem chunk11 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,2,3,6,7,8,9,17])
    (d13 : a 13 ∈ [0,1,3,4])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0,18])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,6,7])
    (d18 : a 18 ∈ [0])
    (d23 : a 23 ∈ [0,1,2])
    (d20 : a 20 ∈ [0,1,3,4])
    (d17 : a 17 ∈ [0,3])
    (d19 : a 19 ∈ [0,1,2])
    (c43 : edge r43 (a 13) (a 28)=true)
    (c45 : edge r45 (a 14) (a 29)=true)
    (c46 : edge r46 (a 15) (a 30)=true)
    (c48 : edge r48 (a 16) (a 18)=true)
    (c49 : edge r49 (a 16) (a 23)=true)
    (c51 : edge r51 (a 17) (a 20)=true)
    (c53 : edge r53 (a 18) (a 19)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    : a 28 ∈ [0,2,6,7,8,9] ∧ a 29 ∈ [0,1,2,3] ∧ a 30 ∈ [0,2,4] ∧ a 16 ∈ [0,6] ∧ a 23 ∈ [0] ∧ a 20 ∈ [0,3] ∧ a 19 ∈ [0] := by
  have b0 : a 28 ≠ 17 := exclude [0,1,3,4] (fun u v => edge r43 v u) (a 28) (a 13) 17 d13 c43 (by decide +kernel)
  have t0 : a 28 ∈ [0,1,2,3,6,7,8,9] := remove (a 28) 17 [0,1,2,3,6,7,8,9,17] d28 b0
  have b1 : a 29 ≠ 4 := exclude [0,18] (fun u v => edge r45 v u) (a 29) (a 14) 4 d14 c45 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,2,3,5] := remove (a 29) 4 [0,1,2,3,4,5] d29 b1
  have b2 : a 29 ≠ 5 := exclude [0,18] (fun u v => edge r45 v u) (a 29) (a 14) 5 d14 c45 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,2,3] := remove (a 29) 5 [0,1,2,3,5] t1 b2
  have b3 : a 30 ≠ 1 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 15) 1 d15 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,3,4,5] := remove (a 30) 1 [0,1,2,3,4,5] d30 b3
  have b4 : a 30 ≠ 3 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 15) 3 d15 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,4,5] := remove (a 30) 3 [0,2,3,4,5] t3 b4
  have b5 : a 30 ≠ 5 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 15) 5 d15 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,4] := remove (a 30) 5 [0,2,4,5] t4 b5
  have b6 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 18) 1 d18 c48 (by decide +kernel)
  have t6 : a 16 ∈ [0,6,7] := remove (a 16) 1 [0,1,6,7] d16 b6
  have b7 : a 16 ≠ 7 := exclude [0] (edge r48) (a 16) (a 18) 7 d18 c48 (by decide +kernel)
  have t7 : a 16 ∈ [0,6] := remove (a 16) 7 [0,6,7] t6 b7
  have b8 : a 23 ≠ 1 := exclude [0,6] (fun u v => edge r49 v u) (a 23) (a 16) 1 t7 c49 (by decide +kernel)
  have t8 : a 23 ∈ [0,2] := remove (a 23) 1 [0,1,2] d23 b8
  have b9 : a 23 ≠ 2 := exclude [0,6] (fun u v => edge r49 v u) (a 23) (a 16) 2 t7 c49 (by decide +kernel)
  have t9 : a 23 ∈ [0] := remove (a 23) 2 [0,2] t8 b9
  have b10 : a 20 ≠ 1 := exclude [0,3] (fun u v => edge r51 v u) (a 20) (a 17) 1 d17 c51 (by decide +kernel)
  have t10 : a 20 ∈ [0,3,4] := remove (a 20) 1 [0,1,3,4] d20 b10
  have b11 : a 20 ≠ 4 := exclude [0,3] (fun u v => edge r51 v u) (a 20) (a 17) 4 d17 c51 (by decide +kernel)
  have t11 : a 20 ∈ [0,3] := remove (a 20) 4 [0,3,4] t10 b11
  have b12 : a 19 ≠ 1 := exclude [0] (fun u v => edge r53 v u) (a 19) (a 18) 1 d18 c53 (by decide +kernel)
  have t12 : a 19 ∈ [0,2] := remove (a 19) 1 [0,1,2] d19 b12
  have b13 : a 19 ≠ 2 := exclude [0] (fun u v => edge r53 v u) (a 19) (a 18) 2 d18 c53 (by decide +kernel)
  have t13 : a 19 ∈ [0] := remove (a 19) 2 [0,2] t12 b13
  have b14 : a 28 ≠ 1 := exclude [0,3] (fun u v => edge r59 v u) (a 28) (a 20) 1 t11 c59 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,3,6,7,8,9] := remove (a 28) 1 [0,1,2,3,6,7,8,9] t0 b14
  have b15 : a 28 ≠ 3 := exclude [0,3] (fun u v => edge r59 v u) (a 28) (a 20) 3 t11 c59 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,6,7,8,9] := remove (a 28) 3 [0,2,3,6,7,8,9] t14 b15
  exact And.intro t15 (And.intro t2 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (t13))))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_189
