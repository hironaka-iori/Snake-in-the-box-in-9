import PartitionData205_162
namespace PartitionCover205_162
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d24 : a 24 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    : a 4 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17] ∧ a 8 ∈ [0,1] ∧ a 24 ∈ [0,1] ∧ a 9 ∈ [0,2] ∧ a 11 ∈ [0,2,5] := by
  have b0 : a 4 ≠ 6 := exclude [0,1,2,3,4,5] (edge r19) (a 4) (a 20) 6 d20 c19 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d4 b0
  have b1 : a 4 ≠ 7 := exclude [0,1,2,3,4,5] (edge r19) (a 4) (a 20) 7 d20 c19 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 4) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 4 ≠ 12 := exclude [0,1,2,3,4,5] (edge r19) (a 4) (a 20) 12 d20 c19 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] := remove (a 4) 12 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 4 ≠ 13 := exclude [0,1,2,3,4,5] (edge r19) (a 4) (a 20) 13 d20 c19 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17] := remove (a 4) 13 [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] t2 b3
  have b4 : a 8 ≠ 2 := exclude [0,1,2] (edge r31) (a 8) (a 24) 2 d24 c31 (by decide +kernel)
  have t4 : a 8 ∈ [0,1,3,4,5] := remove (a 8) 2 [0,1,2,3,4,5] d8 b4
  have b5 : a 8 ≠ 3 := exclude [0,1,2] (edge r31) (a 8) (a 24) 3 d24 c31 (by decide +kernel)
  have t5 : a 8 ∈ [0,1,4,5] := remove (a 8) 3 [0,1,3,4,5] t4 b5
  have b6 : a 8 ≠ 4 := exclude [0,1,2] (edge r31) (a 8) (a 24) 4 d24 c31 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,5] := remove (a 8) 4 [0,1,4,5] t5 b6
  have b7 : a 8 ≠ 5 := exclude [0,1,2] (edge r31) (a 8) (a 24) 5 d24 c31 (by decide +kernel)
  have t7 : a 8 ∈ [0,1] := remove (a 8) 5 [0,1,5] t6 b7
  have b8 : a 24 ≠ 2 := exclude [0,1] (fun u v => edge r31 v u) (a 24) (a 8) 2 t7 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0,1] := remove (a 24) 2 [0,1,2] d24 b8
  have b9 : a 9 ≠ 1 := exclude [0,1,2,3,4,5] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t9 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b9
  have b10 : a 9 ≠ 3 := exclude [0,1,2,3,4,5] (edge r32) (a 9) (a 11) 3 d11 c32 (by decide +kernel)
  have t10 : a 9 ∈ [0,2,4,5] := remove (a 9) 3 [0,2,3,4,5] t9 b10
  have b11 : a 9 ≠ 4 := exclude [0,1,2,3,4,5] (edge r32) (a 9) (a 11) 4 d11 c32 (by decide +kernel)
  have t11 : a 9 ∈ [0,2,5] := remove (a 9) 4 [0,2,4,5] t10 b11
  have b12 : a 9 ≠ 5 := exclude [0,1,2,3,4,5] (edge r32) (a 9) (a 11) 5 d11 c32 (by decide +kernel)
  have t12 : a 9 ∈ [0,2] := remove (a 9) 5 [0,2,5] t11 b12
  have b13 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 1 t12 c32 (by decide +kernel)
  have t13 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b13
  have b14 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 3 t12 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,4,5] := remove (a 11) 3 [0,2,3,4,5] t13 b14
  have b15 : a 11 ≠ 4 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 4 t12 c32 (by decide +kernel)
  have t15 : a 11 ∈ [0,2,5] := remove (a 11) 4 [0,2,4,5] t14 b15
  exact And.intro t3 (And.intro t7 (And.intro t8 (And.intro t12 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,2,5])
    (d9 : a 9 ∈ [0,2])
    (d25 : a 25 ∈ [0,1,2])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d10 : a 10 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 11 ∈ [0,2] ∧ a 25 ∈ [0] ∧ a 14 ∈ [0,2,6,8,12,14] ∧ a 27 ∈ [0,2,3,4,5] := by
  have b0 : a 11 ≠ 5 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 9) 5 d9 c32 (by decide +kernel)
  have t0 : a 11 ∈ [0,2] := remove (a 11) 5 [0,2,5] d11 b0
  have b1 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,2] := remove (a 25) 1 [0,1,2] d25 b1
  have b2 : a 25 ≠ 2 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 2 [0,2] t1 b2
  have b3 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d14 b3
  have b4 : a 14 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 3 d10 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 14 ≠ 4 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 4 d10 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 14 ≠ 5 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 14 ≠ 7 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 7 d10 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17] := remove (a 14) 7 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 14 ≠ 9 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 9 d10 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,6,8,10,11,12,13,14,15,16,17] := remove (a 14) 9 [0,2,6,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 14 ≠ 10 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 10 d10 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,2,6,8,11,12,13,14,15,16,17] := remove (a 14) 10 [0,2,6,8,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 14 ≠ 11 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 11 d10 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,2,6,8,12,13,14,15,16,17] := remove (a 14) 11 [0,2,6,8,11,12,13,14,15,16,17] t9 b10
  have b11 : a 14 ≠ 13 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 13 d10 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,6,8,12,14,15,16,17] := remove (a 14) 13 [0,2,6,8,12,13,14,15,16,17] t10 b11
  have b12 : a 14 ≠ 15 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 15 d10 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0,2,6,8,12,14,16,17] := remove (a 14) 15 [0,2,6,8,12,14,15,16,17] t11 b12
  have b13 : a 14 ≠ 16 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 16 d10 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,6,8,12,14,17] := remove (a 14) 16 [0,2,6,8,12,14,16,17] t12 b13
  have b14 : a 14 ≠ 17 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 17 d10 c36 (by decide +kernel)
  have t14 : a 14 ∈ [0,2,6,8,12,14] := remove (a 14) 17 [0,2,6,8,12,14,17] t13 b14
  have b15 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 1 t0 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b15
  exact And.intro t0 (And.intro t2 (And.intro t14 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2,3,4,5])
    (d11 : a 11 ∈ [0,2])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8])
    (d14 : a 14 ∈ [0,2,6,8,12,14])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d16 : a 16 ∈ [0])
    (d19 : a 19 ∈ [0,1,2])
    (d17 : a 17 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 27 ∈ [0,2] ∧ a 30 ∈ [0,1,3,4,6,7] ∧ a 20 ∈ [0,1,4,5] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,2,4,5] := remove (a 27) 3 [0,2,3,4,5] d27 b0
  have b1 : a 27 ≠ 4 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,5] := remove (a 27) 4 [0,2,4,5] t0 b1
  have b2 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,2] := remove (a 27) 5 [0,2,5] t1 b2
  have b3 : a 30 ≠ 2 := exclude [0,2,6,8,12,14] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,3,4,5,6,7,8] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8] d30 b3
  have b4 : a 30 ≠ 5 := exclude [0,2,6,8,12,14] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,3,4,6,7,8] := remove (a 30) 5 [0,1,3,4,5,6,7,8] t3 b4
  have b5 : a 30 ≠ 8 := exclude [0,2,6,8,12,14] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,3,4,6,7] := remove (a 30) 8 [0,1,3,4,6,7,8] t4 b5
  have b6 : a 20 ≠ 2 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 2 d16 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,3,4,5] := remove (a 20) 2 [0,1,2,3,4,5] d20 b6
  have b7 : a 20 ≠ 3 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 3 d16 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,4,5] := remove (a 20) 3 [0,1,3,4,5] t6 b7
  have b8 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t8 : a 19 ∈ [0,2] := remove (a 19) 1 [0,1,2] d19 b8
  have b9 : a 19 ≠ 2 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 2 d17 c52 (by decide +kernel)
  have t9 : a 19 ∈ [0] := remove (a 19) 2 [0,2] t8 b9
  have b10 : a 21 ≠ 2 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t10 : a 21 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d21 b10
  have b11 : a 21 ≠ 3 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 3 d17 c53 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 21 ≠ 4 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t12 : a 21 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 21 ≠ 5 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 5 d17 c53 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 21 ≠ 6 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 6 d17 c53 (by decide +kernel)
  have t14 : a 21 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 21 ≠ 7 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 7 d17 c53 (by decide +kernel)
  have t15 : a 21 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 21) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t2 (And.intro t5 (And.intro t7 (And.intro t9 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,8,9,10,11,12,13,14,15,16,17])
    (d17 : a 17 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (d18 : a 18 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2])
    (c53 : edge r53 (a 17) (a 21)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    : a 21 ∈ [0,1] ∧ a 22 ∈ [0,2,7,8] ∧ a 26 ∈ [0,1] := by
  have b0 : a 21 ≠ 8 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 8 d17 c53 (by decide +kernel)
  have t0 : a 21 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 21) 8 [0,1,8,9,10,11,12,13,14,15,16,17] d21 b0
  have b1 : a 21 ≠ 9 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 9 d17 c53 (by decide +kernel)
  have t1 : a 21 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 21) 9 [0,1,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 21 ≠ 10 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 10 d17 c53 (by decide +kernel)
  have t2 : a 21 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 21) 10 [0,1,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 21 ≠ 11 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 11 d17 c53 (by decide +kernel)
  have t3 : a 21 ∈ [0,1,12,13,14,15,16,17] := remove (a 21) 11 [0,1,11,12,13,14,15,16,17] t2 b3
  have b4 : a 21 ≠ 12 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 12 d17 c53 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,13,14,15,16,17] := remove (a 21) 12 [0,1,12,13,14,15,16,17] t3 b4
  have b5 : a 21 ≠ 13 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 13 d17 c53 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,14,15,16,17] := remove (a 21) 13 [0,1,13,14,15,16,17] t4 b5
  have b6 : a 21 ≠ 14 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 14 d17 c53 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,15,16,17] := remove (a 21) 14 [0,1,14,15,16,17] t5 b6
  have b7 : a 21 ≠ 15 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 15 d17 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,16,17] := remove (a 21) 15 [0,1,15,16,17] t6 b7
  have b8 : a 21 ≠ 16 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 16 d17 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,17] := remove (a 21) 16 [0,1,16,17] t7 b8
  have b9 : a 21 ≠ 17 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 17 d17 c53 (by decide +kernel)
  have t9 : a 21 ∈ [0,1] := remove (a 21) 17 [0,1,17] t8 b9
  have b10 : a 22 ≠ 1 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t10 : a 22 ∈ [0,2,3,4,5,6,7,8] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8] d22 b10
  have b11 : a 22 ≠ 3 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 3 d18 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,4,5,6,7,8] := remove (a 22) 3 [0,2,3,4,5,6,7,8] t10 b11
  have b12 : a 22 ≠ 4 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 4 d18 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,5,6,7,8] := remove (a 22) 4 [0,2,4,5,6,7,8] t11 b12
  have b13 : a 22 ≠ 5 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 5 d18 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,6,7,8] := remove (a 22) 5 [0,2,5,6,7,8] t12 b13
  have b14 : a 22 ≠ 6 := exclude [0,1] (fun u v => edge r56 v u) (a 22) (a 18) 6 d18 c56 (by decide +kernel)
  have t14 : a 22 ∈ [0,2,7,8] := remove (a 22) 6 [0,2,6,7,8] t13 b14
  have b15 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r57 v u) (a 26) (a 18) 2 d18 c57 (by decide +kernel)
  have t15 : a 26 ∈ [0,1] := remove (a 26) 2 [0,1,2] d26 b15
  exact And.intro t9 (And.intro t14 (t15))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_162
