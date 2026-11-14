import PartitionData205_163
namespace PartitionCover205_163
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,18,19])
    (d7 : a 7 ∈ [0])
    (d8 : a 8 ∈ [0,1,2])
    (d9 : a 9 ∈ [0])
    (d10 : a 10 ∈ [0,1,2])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 23 ∈ [0,1,2,3,4,5,6,7] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 24 ∈ [0,4,10,13,14,15,16,17] := by
  have b0 : a 23 ≠ 18 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 18 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,2,3,4,5,6,7,19] := remove (a 23) 18 [0,1,2,3,4,5,6,7,18,19] d23 b0
  have b1 : a 23 ≠ 19 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 19 d7 c27 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,2,3,4,5,6,7] := remove (a 23) 19 [0,1,2,3,4,5,6,7,19] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t2 : a 8 ∈ [0,2] := remove (a 8) 1 [0,1,2] d8 b2
  have b3 : a 8 ≠ 2 := exclude [0] (edge r28) (a 8) (a 9) 2 d9 c28 (by decide +kernel)
  have t3 : a 8 ∈ [0] := remove (a 8) 2 [0,2] t2 b3
  have b4 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 t3 c29 (by decide +kernel)
  have t4 : a 10 ∈ [0,2] := remove (a 10) 1 [0,1,2] d10 b4
  have b5 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 t3 c29 (by decide +kernel)
  have t5 : a 10 ∈ [0] := remove (a 10) 2 [0,2] t4 b5
  have b6 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 t3 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d24 b6
  have b7 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 t3 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 t3 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 24 ≠ 5 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 5 t3 c31 (by decide +kernel)
  have t9 : a 24 ∈ [0,4,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 5 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 t3 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0,4,7,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 6 [0,4,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 24 ≠ 7 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 7 t3 c31 (by decide +kernel)
  have t11 : a 24 ∈ [0,4,8,9,10,11,12,13,14,15,16,17] := remove (a 24) 7 [0,4,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 t3 c31 (by decide +kernel)
  have t12 : a 24 ∈ [0,4,9,10,11,12,13,14,15,16,17] := remove (a 24) 8 [0,4,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 24 ≠ 9 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 9 t3 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0,4,10,11,12,13,14,15,16,17] := remove (a 24) 9 [0,4,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 24 ≠ 11 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 11 t3 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,4,10,12,13,14,15,16,17] := remove (a 24) 11 [0,4,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 24 ≠ 12 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 12 t3 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,4,10,13,14,15,16,17] := remove (a 24) 12 [0,4,10,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,4,10,13,14,15,16,17])
    (d8 : a 8 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 24 ∈ [0,4,10] ∧ a 11 ∈ [0] ∧ a 25 ∈ [0,1,4] ∧ a 26 ∈ [0,4,5,6,7] := by
  have b0 : a 24 ≠ 13 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 13 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,4,10,14,15,16,17] := remove (a 24) 13 [0,4,10,13,14,15,16,17] d24 b0
  have b1 : a 24 ≠ 14 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 14 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,4,10,15,16,17] := remove (a 24) 14 [0,4,10,14,15,16,17] t0 b1
  have b2 : a 24 ≠ 15 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 15 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,4,10,16,17] := remove (a 24) 15 [0,4,10,15,16,17] t1 b2
  have b3 : a 24 ≠ 16 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 16 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,4,10,17] := remove (a 24) 16 [0,4,10,16,17] t2 b3
  have b4 : a 24 ≠ 17 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 17 d8 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0,4,10] := remove (a 24) 17 [0,4,10,17] t3 b4
  have b5 : a 11 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 1 d9 c32 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0,3,4,5] := remove (a 11) 2 [0,2,3,4,5] t5 b6
  have b7 : a 11 ≠ 3 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t7 : a 11 ∈ [0,4,5] := remove (a 11) 3 [0,3,4,5] t6 b7
  have b8 : a 11 ≠ 4 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 4 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0,5] := remove (a 11) 4 [0,4,5] t7 b8
  have b9 : a 25 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,3,4,5] := remove (a 25) 2 [0,1,2,3,4,5] d25 b9
  have b10 : a 25 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,4,5] := remove (a 25) 3 [0,1,3,4,5] t9 b10
  have b11 : a 25 ≠ 5 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,4] := remove (a 25) 5 [0,1,4,5] t10 b11
  have b12 : a 11 ≠ 5 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 5 d10 c35 (by decide +kernel)
  have t12 : a 11 ∈ [0] := remove (a 11) 5 [0,5] t8 b12
  have b13 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,3,4,5,6,7] := remove (a 26) 1 [0,1,2,3,4,5,6,7] d26 b13
  have b14 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,3,4,5,6,7] := remove (a 26) 2 [0,2,3,4,5,6,7] t13 b14
  have b15 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,4,5,6,7] := remove (a 26) 3 [0,3,4,5,6,7] t14 b15
  exact And.intro t4 (And.intro t12 (And.intro t11 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,4,5,6,7])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 26 ∈ [0,6] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0,1,10,11] := by
  have b0 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,5,6,7] := remove (a 26) 4 [0,4,5,6,7] d26 b0
  have b1 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,6,7] := remove (a 26) 5 [0,5,6,7] t0 b1
  have b2 : a 26 ≠ 7 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,6] := remove (a 26) 7 [0,6,7] t1 b2
  have b3 : a 15 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t3 : a 15 ∈ [0,2,3,4,5] := remove (a 15) 1 [0,1,2,3,4,5] d15 b3
  have b4 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t4 : a 15 ∈ [0,3,4,5] := remove (a 15) 2 [0,2,3,4,5] t3 b4
  have b5 : a 15 ≠ 3 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t5 : a 15 ∈ [0,4,5] := remove (a 15) 3 [0,3,4,5] t4 b5
  have b6 : a 15 ≠ 4 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 4 d11 c38 (by decide +kernel)
  have t6 : a 15 ∈ [0,5] := remove (a 15) 4 [0,4,5] t5 b6
  have b7 : a 15 ≠ 5 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 5 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0] := remove (a 15) 5 [0,5] t6 b7
  have b8 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d27 b8
  have b9 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,6,7,8,9,10,11] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11] t10 b11
  have b12 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,7,8,9,10,11] := remove (a 27) 6 [0,1,6,7,8,9,10,11] t11 b12
  have b13 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,8,9,10,11] := remove (a 27) 7 [0,1,7,8,9,10,11] t12 b13
  have b14 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,9,10,11] := remove (a 27) 8 [0,1,8,9,10,11] t13 b14
  have b15 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,10,11] := remove (a 27) 9 [0,1,9,10,11] t14 b15
  exact And.intro t2 (And.intro t7 (t15))

theorem chunk7 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,10,11])
    (d11 : a 11 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d12 : a 12 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d15 : a 15 ∈ [0])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 27 ∈ [0,1] ∧ a 28 ∈ [0,1] ∧ a 30 ∈ [0,2] ∧ a 31 ∈ [0,1,2,3,5,6,7,8,9] := by
  have b0 : a 27 ≠ 10 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,11] := remove (a 27) 10 [0,1,10,11] d27 b0
  have b1 : a 27 ≠ 11 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1] := remove (a 27) 11 [0,1,11] t0 b1
  have b2 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 28) 2 [0,1,2,3,4,5,6,7,8,9] d28 b2
  have b3 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,1,4,5,6,7,8,9] := remove (a 28) 3 [0,1,3,4,5,6,7,8,9] t2 b3
  have b4 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,1,5,6,7,8,9] := remove (a 28) 4 [0,1,4,5,6,7,8,9] t3 b4
  have b5 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,6,7,8,9] := remove (a 28) 5 [0,1,5,6,7,8,9] t4 b5
  have b6 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,7,8,9] := remove (a 28) 6 [0,1,6,7,8,9] t5 b6
  have b7 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,8,9] := remove (a 28) 7 [0,1,7,8,9] t6 b7
  have b8 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,9] := remove (a 28) 8 [0,1,8,9] t7 b8
  have b9 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1] := remove (a 28) 9 [0,1,9] t8 b9
  have b10 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,3,4,5,6] := remove (a 30) 1 [0,1,2,3,4,5,6] d30 b10
  have b11 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,4,5,6] := remove (a 30) 3 [0,2,3,4,5,6] t10 b11
  have b12 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,5,6] := remove (a 30) 4 [0,2,4,5,6] t11 b12
  have b13 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,6] := remove (a 30) 5 [0,2,5,6] t12 b13
  have b14 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,2] := remove (a 30) 6 [0,2,6] t13 b14
  have b15 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,3,5,6,7,8,9] := remove (a 31) 4 [0,1,2,3,4,5,6,7,8,9] d31 b15
  exact And.intro t1 (And.intro t9 (And.intro t14 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_163
