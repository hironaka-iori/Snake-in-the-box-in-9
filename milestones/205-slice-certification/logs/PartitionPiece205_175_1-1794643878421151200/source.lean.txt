import PartitionData205_175
namespace PartitionCover205_175
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17])
    (d7 : a 7 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,1,2,5])
    (d12 : a 12 ∈ [0,1,10,11])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 15 ∈ [0,1,2,3,4,5,12,13,14,15,16,17] ∧ a 10 ∈ [0,1,2,5] ∧ a 8 ∈ [0,1] ∧ a 24 ∈ [0,1,2,3,5,7,9,11,13,15,17,19] := by
  have b0 : a 15 ≠ 8 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] := remove (a 15) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] d15 b0
  have b1 : a 15 ≠ 9 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17] := remove (a 15) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 15 ≠ 10 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 10 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17] := remove (a 15) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 15 ≠ 11 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 11 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,2,3,4,5,12,13,14,15,16,17] := remove (a 15) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17] t2 b3
  have b4 : a 10 ≠ 3 := exclude [0,1,2,5] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t4 : a 10 ∈ [0,1,2,4,5] := remove (a 10) 3 [0,1,2,3,4,5] d10 b4
  have b5 : a 10 ≠ 4 := exclude [0,1,2,5] (fun u v => edge r29 v u) (a 10) (a 8) 4 d8 c29 (by decide +kernel)
  have t5 : a 10 ∈ [0,1,2,5] := remove (a 10) 4 [0,1,2,4,5] t4 b5
  have b6 : a 8 ≠ 2 := exclude [0,1,10,11] (edge r30) (a 8) (a 12) 2 d12 c30 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,5] := remove (a 8) 2 [0,1,2,5] d8 b6
  have b7 : a 8 ≠ 5 := exclude [0,1,10,11] (edge r30) (a 8) (a 12) 5 d12 c30 (by decide +kernel)
  have t7 : a 8 ∈ [0,1] := remove (a 8) 5 [0,1,5] t6 b7
  have b8 : a 24 ≠ 4 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 4 t7 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 24) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d24 b8
  have b9 : a 24 ≠ 6 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 6 t7 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,1,2,3,5,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 24) 6 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 24 ≠ 8 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 8 t7 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,1,2,3,5,7,9,10,11,12,13,14,15,16,17,18,19] := remove (a 24) 8 [0,1,2,3,5,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 24 ≠ 10 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 10 t7 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,2,3,5,7,9,11,12,13,14,15,16,17,18,19] := remove (a 24) 10 [0,1,2,3,5,7,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 24 ≠ 12 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 12 t7 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,2,3,5,7,9,11,13,14,15,16,17,18,19] := remove (a 24) 12 [0,1,2,3,5,7,9,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 24 ≠ 14 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 14 t7 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,1,2,3,5,7,9,11,13,15,16,17,18,19] := remove (a 24) 14 [0,1,2,3,5,7,9,11,13,14,15,16,17,18,19] t12 b13
  have b14 : a 24 ≠ 16 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 16 t7 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,1,2,3,5,7,9,11,13,15,17,18,19] := remove (a 24) 16 [0,1,2,3,5,7,9,11,13,15,16,17,18,19] t13 b14
  have b15 : a 24 ≠ 18 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 18 t7 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,1,2,3,5,7,9,11,13,15,17,19] := remove (a 24) 18 [0,1,2,3,5,7,9,11,13,15,17,18,19] t14 b15
  exact And.intro t3 (And.intro t5 (And.intro t7 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d9 : a 9 ∈ [0,4])
    (d10 : a 10 ∈ [0,1,2,5])
    (d11 : a 11 ∈ [0,2,6,8])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1,2,3,4,5,12,13,14,15,16,17])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 25 ∈ [0] ∧ a 10 ∈ [0,1] ∧ a 14 ∈ [0,3] ∧ a 15 ∈ [0,1,3,4,5,12,13,14,15,16,17] := by
  have b0 : a 25 ≠ 1 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0,2,3,4,5,6,7,8,9] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9] d25 b0
  have b1 : a 25 ≠ 2 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,3,4,5,6,7,8,9] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9] t0 b1
  have b2 : a 25 ≠ 3 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,4,5,6,7,8,9] := remove (a 25) 3 [0,3,4,5,6,7,8,9] t1 b2
  have b3 : a 25 ≠ 4 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,5,6,7,8,9] := remove (a 25) 4 [0,4,5,6,7,8,9] t2 b3
  have b4 : a 25 ≠ 5 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,6,7,8,9] := remove (a 25) 5 [0,5,6,7,8,9] t3 b4
  have b5 : a 25 ≠ 6 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,7,8,9] := remove (a 25) 6 [0,6,7,8,9] t4 b5
  have b6 : a 25 ≠ 7 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,8,9] := remove (a 25) 7 [0,7,8,9] t5 b6
  have b7 : a 25 ≠ 8 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,9] := remove (a 25) 8 [0,8,9] t6 b7
  have b8 : a 25 ≠ 9 := exclude [0,4] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0] := remove (a 25) 9 [0,9] t7 b8
  have b9 : a 10 ≠ 2 := exclude [0,2,6,8] (edge r35) (a 10) (a 11) 2 d11 c35 (by decide +kernel)
  have t9 : a 10 ∈ [0,1,5] := remove (a 10) 2 [0,1,2,5] d10 b9
  have b10 : a 10 ≠ 5 := exclude [0,2,6,8] (edge r35) (a 10) (a 11) 5 d11 c35 (by decide +kernel)
  have t10 : a 10 ∈ [0,1] := remove (a 10) 5 [0,1,5] t9 b10
  have b11 : a 14 ≠ 1 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 1 t10 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b11
  have b12 : a 14 ≠ 2 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 2 t10 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0,3,4,5] := remove (a 14) 2 [0,2,3,4,5] t11 b12
  have b13 : a 14 ≠ 4 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 4 t10 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,3,5] := remove (a 14) 4 [0,3,4,5] t12 b13
  have b14 : a 14 ≠ 5 := exclude [0,1] (fun u v => edge r36 v u) (a 14) (a 10) 5 t10 c36 (by decide +kernel)
  have t14 : a 14 ∈ [0,3] := remove (a 14) 5 [0,3,5] t13 b14
  have b15 : a 15 ≠ 2 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,3,4,5,12,13,14,15,16,17] := remove (a 15) 2 [0,1,2,3,4,5,12,13,14,15,16,17] d15 b15
  exact And.intro t8 (And.intro t10 (And.intro t14 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,3,4,5,12,13,14,15,16,17])
    (d11 : a 11 ∈ [0,2,6,8])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,9,10,11])
    (d12 : a 12 ∈ [0,1,10,11])
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    : a 15 ∈ [0,1,12,13] ∧ a 27 ∈ [0,1,3,4] ∧ a 13 ∈ [0,5,11] := by
  have b0 : a 15 ≠ 3 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,4,5,12,13,14,15,16,17] := remove (a 15) 3 [0,1,3,4,5,12,13,14,15,16,17] d15 b0
  have b1 : a 15 ≠ 4 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,5,12,13,14,15,16,17] := remove (a 15) 4 [0,1,4,5,12,13,14,15,16,17] t0 b1
  have b2 : a 15 ≠ 5 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,12,13,14,15,16,17] := remove (a 15) 5 [0,1,5,12,13,14,15,16,17] t1 b2
  have b3 : a 15 ≠ 14 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 14 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,12,13,15,16,17] := remove (a 15) 14 [0,1,12,13,14,15,16,17] t2 b3
  have b4 : a 15 ≠ 15 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 15 d11 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,12,13,16,17] := remove (a 15) 15 [0,1,12,13,15,16,17] t3 b4
  have b5 : a 15 ≠ 16 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 16 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,12,13,17] := remove (a 15) 16 [0,1,12,13,16,17] t4 b5
  have b6 : a 15 ≠ 17 := exclude [0,2,6,8] (fun u v => edge r38 v u) (a 15) (a 11) 17 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,12,13] := remove (a 15) 17 [0,1,12,13,17] t5 b6
  have b7 : a 27 ≠ 2 := exclude [0,2,6,8] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,3,4,5] := remove (a 27) 2 [0,1,2,3,4,5] d27 b7
  have b8 : a 27 ≠ 5 := exclude [0,2,6,8] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,3,4] := remove (a 27) 5 [0,1,3,4,5] t7 b8
  have b9 : a 13 ≠ 1 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 1 d12 c40 (by decide +kernel)
  have t9 : a 13 ∈ [0,2,3,4,5,6,9,10,11] := remove (a 13) 1 [0,1,2,3,4,5,6,9,10,11] d13 b9
  have b10 : a 13 ≠ 2 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 2 d12 c40 (by decide +kernel)
  have t10 : a 13 ∈ [0,3,4,5,6,9,10,11] := remove (a 13) 2 [0,2,3,4,5,6,9,10,11] t9 b10
  have b11 : a 13 ≠ 3 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 3 d12 c40 (by decide +kernel)
  have t11 : a 13 ∈ [0,4,5,6,9,10,11] := remove (a 13) 3 [0,3,4,5,6,9,10,11] t10 b11
  have b12 : a 13 ≠ 4 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 4 d12 c40 (by decide +kernel)
  have t12 : a 13 ∈ [0,5,6,9,10,11] := remove (a 13) 4 [0,4,5,6,9,10,11] t11 b12
  have b13 : a 13 ≠ 6 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 6 d12 c40 (by decide +kernel)
  have t13 : a 13 ∈ [0,5,9,10,11] := remove (a 13) 6 [0,5,6,9,10,11] t12 b13
  have b14 : a 13 ≠ 9 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 9 d12 c40 (by decide +kernel)
  have t14 : a 13 ∈ [0,5,10,11] := remove (a 13) 9 [0,5,9,10,11] t13 b14
  have b15 : a 13 ≠ 10 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 10 d12 c40 (by decide +kernel)
  have t15 : a 13 ∈ [0,5,11] := remove (a 13) 10 [0,5,10,11] t14 b15
  exact And.intro t6 (And.intro t8 (t15))

theorem chunk7 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,5,11])
    (d12 : a 12 ∈ [0,1,10,11])
    (d28 : a 28 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1,12,13])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
    (d14 : a 14 ∈ [0,3])
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 13 ∈ [0] ∧ a 28 ∈ [0,3] ∧ a 15 ∈ [0,13] ∧ a 30 ∈ [0,1,2,3,12,13,14,15,16,17,18,19] := by
  have b0 : a 13 ≠ 11 := exclude [0,1,10,11] (fun u v => edge r40 v u) (a 13) (a 12) 11 d12 c40 (by decide +kernel)
  have t0 : a 13 ∈ [0,5] := remove (a 13) 11 [0,5,11] d13 b0
  have b1 : a 28 ≠ 1 := exclude [0,1,10,11] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,3,4,5] := remove (a 28) 1 [0,1,2,3,4,5] d28 b1
  have b2 : a 28 ≠ 2 := exclude [0,1,10,11] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,3,4,5] := remove (a 28) 2 [0,2,3,4,5] t1 b2
  have b3 : a 28 ≠ 4 := exclude [0,1,10,11] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,3,5] := remove (a 28) 4 [0,3,4,5] t2 b3
  have b4 : a 28 ≠ 5 := exclude [0,1,10,11] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,3] := remove (a 28) 5 [0,3,5] t3 b4
  have b5 : a 13 ≠ 5 := exclude [0,1,12,13] (edge r43) (a 13) (a 15) 5 d15 c43 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 5 [0,5] t0 b5
  have b6 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 t5 c43 (by decide +kernel)
  have t6 : a 15 ∈ [0,12,13] := remove (a 15) 1 [0,1,12,13] d15 b6
  have b7 : a 15 ≠ 12 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 12 t5 c43 (by decide +kernel)
  have t7 : a 15 ∈ [0,13] := remove (a 15) 12 [0,12,13] t6 b7
  have b8 : a 30 ≠ 4 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 4 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] d30 b8
  have b9 : a 30 ≠ 5 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 5 [0,1,2,3,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t8 b9
  have b10 : a 30 ≠ 6 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 6 [0,1,2,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19] t9 b10
  have b11 : a 30 ≠ 7 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 7 [0,1,2,3,7,8,9,10,11,12,13,14,15,16,17,18,19] t10 b11
  have b12 : a 30 ≠ 8 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 8 [0,1,2,3,8,9,10,11,12,13,14,15,16,17,18,19] t11 b12
  have b13 : a 30 ≠ 9 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,2,3,10,11,12,13,14,15,16,17,18,19] := remove (a 30) 9 [0,1,2,3,9,10,11,12,13,14,15,16,17,18,19] t12 b13
  have b14 : a 30 ≠ 10 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,2,3,11,12,13,14,15,16,17,18,19] := remove (a 30) 10 [0,1,2,3,10,11,12,13,14,15,16,17,18,19] t13 b14
  have b15 : a 30 ≠ 11 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,2,3,12,13,14,15,16,17,18,19] := remove (a 30) 11 [0,1,2,3,11,12,13,14,15,16,17,18,19] t14 b15
  exact And.intro t5 (And.intro t4 (And.intro t7 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_175
