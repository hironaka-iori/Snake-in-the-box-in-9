import PartitionData205_179
namespace PartitionCover205_179
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17])
    (d7 : a 7 ∈ [0,2])
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0])
    (d12 : a 12 ∈ [0,1,3,5])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0])
    (d14 : a 14 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 23 ∈ [0,1,2,3,4,5,12,13,14,15,16,17] ∧ a 8 ∈ [0,1] ∧ a 12 ∈ [0,1] ∧ a 9 ∈ [0] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0,4,5] := by
  have b0 : a 23 ≠ 11 := exclude [0,2] (fun u v => edge r27 v u) (a 23) (a 7) 11 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,1,2,3,4,5,12,13,14,15,16,17] := remove (a 23) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17] d23 b0
  have b1 : a 8 ≠ 2 := exclude [0] (edge r29) (a 8) (a 10) 2 d10 c29 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,3,4,5] := remove (a 8) 2 [0,1,2,3,4,5] d8 b1
  have b2 : a 8 ≠ 3 := exclude [0] (edge r29) (a 8) (a 10) 3 d10 c29 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,4,5] := remove (a 8) 3 [0,1,3,4,5] t1 b2
  have b3 : a 8 ≠ 4 := exclude [0] (edge r29) (a 8) (a 10) 4 d10 c29 (by decide +kernel)
  have t3 : a 8 ∈ [0,1,5] := remove (a 8) 4 [0,1,4,5] t2 b3
  have b4 : a 8 ≠ 5 := exclude [0] (edge r29) (a 8) (a 10) 5 d10 c29 (by decide +kernel)
  have t4 : a 8 ∈ [0,1] := remove (a 8) 5 [0,1,5] t3 b4
  have b5 : a 12 ≠ 3 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 3 t4 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,5] := remove (a 12) 3 [0,1,3,5] d12 b5
  have b6 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r30 v u) (a 12) (a 8) 5 t4 c30 (by decide +kernel)
  have t6 : a 12 ∈ [0,1] := remove (a 12) 5 [0,1,5] t5 b6
  have b7 : a 9 ≠ 1 := exclude [0] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t7 : a 9 ∈ [0,2,3,4,5] := remove (a 9) 1 [0,1,2,3,4,5] d9 b7
  have b8 : a 9 ≠ 2 := exclude [0] (edge r32) (a 9) (a 11) 2 d11 c32 (by decide +kernel)
  have t8 : a 9 ∈ [0,3,4,5] := remove (a 9) 2 [0,2,3,4,5] t7 b8
  have b9 : a 9 ≠ 3 := exclude [0] (edge r32) (a 9) (a 11) 3 d11 c32 (by decide +kernel)
  have t9 : a 9 ∈ [0,4,5] := remove (a 9) 3 [0,3,4,5] t8 b9
  have b10 : a 9 ≠ 4 := exclude [0] (edge r32) (a 9) (a 11) 4 d11 c32 (by decide +kernel)
  have t10 : a 9 ∈ [0,5] := remove (a 9) 4 [0,4,5] t9 b10
  have b11 : a 9 ≠ 5 := exclude [0] (edge r32) (a 9) (a 11) 5 d11 c32 (by decide +kernel)
  have t11 : a 9 ∈ [0] := remove (a 9) 5 [0,5] t10 b11
  have b12 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 d10 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b12
  have b13 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,3,4,5] := remove (a 26) 1 [0,1,2,3,4,5] d26 b13
  have b14 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,3,4,5] := remove (a 26) 2 [0,2,3,4,5] t13 b14
  have b15 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 d10 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,4,5] := remove (a 26) 3 [0,3,4,5] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t6 (And.intro t11 (And.intro t12 (t15)))))

theorem chunk5 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,4,5])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d12 : a 12 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 26 ∈ [0,5] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,1] ∧ a 12 ∈ [0] ∧ a 28 ∈ [0,1,2,7,8] := by
  have b0 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,5] := remove (a 26) 4 [0,4,5] d26 b0
  have b1 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,3] := remove (a 15) 2 [0,1,2,3] d15 b1
  have b2 : a 15 ≠ 3 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0,1] := remove (a 15) 3 [0,1,3] t1 b2
  have b3 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9] d27 b3
  have b4 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,4,5,6,7,8,9] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9] t3 b4
  have b5 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,5,6,7,8,9] := remove (a 27) 4 [0,1,4,5,6,7,8,9] t4 b5
  have b6 : a 27 ≠ 5 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,6,7,8,9] := remove (a 27) 5 [0,1,5,6,7,8,9] t5 b6
  have b7 : a 27 ≠ 6 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,7,8,9] := remove (a 27) 6 [0,1,6,7,8,9] t6 b7
  have b8 : a 27 ≠ 7 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,8,9] := remove (a 27) 7 [0,1,7,8,9] t7 b8
  have b9 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,9] := remove (a 27) 8 [0,1,8,9] t8 b9
  have b10 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1] := remove (a 27) 9 [0,1,9] t9 b10
  have b11 : a 12 ≠ 1 := exclude [0] (edge r41) (a 12) (a 14) 1 d14 c41 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b11
  have b12 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 t11 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,1,2,4,5,6,7,8] := remove (a 28) 3 [0,1,2,3,4,5,6,7,8] d28 b12
  have b13 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 t11 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,1,2,5,6,7,8] := remove (a 28) 4 [0,1,2,4,5,6,7,8] t12 b13
  have b14 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 t11 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,1,2,6,7,8] := remove (a 28) 5 [0,1,2,5,6,7,8] t13 b14
  have b15 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 t11 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,1,2,7,8] := remove (a 28) 6 [0,1,2,6,7,8] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t10 (And.intro t11 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,2,7,8])
    (d12 : a 12 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d30 : a 30 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    : a 28 ∈ [0,1,2] ∧ a 15 ∈ [0] ∧ a 13 ∈ [0] ∧ a 29 ∈ [0,1,2,3,4,5] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,1,2,8] := remove (a 28) 7 [0,1,2,7,8] d28 b0
  have b1 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,1,2] := remove (a 28) 8 [0,1,2,8] t0 b1
  have b2 : a 15 ≠ 1 := exclude [0,1] (fun u v => edge r43 v u) (a 15) (a 13) 1 d13 c43 (by decide +kernel)
  have t2 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b2
  have b3 : a 13 ≠ 1 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r44) (a 13) (a 29) 1 d29 c44 (by decide +kernel)
  have t3 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b3
  have b4 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 t3 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,2,3,4,5,7,8,9,10,11] := remove (a 29) 6 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b4
  have b5 : a 29 ≠ 7 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 7 t3 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,2,3,4,5,8,9,10,11] := remove (a 29) 7 [0,1,2,3,4,5,7,8,9,10,11] t4 b5
  have b6 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 t3 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,2,3,4,5,9,10,11] := remove (a 29) 8 [0,1,2,3,4,5,8,9,10,11] t5 b6
  have b7 : a 29 ≠ 9 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 9 t3 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,2,3,4,5,10,11] := remove (a 29) 9 [0,1,2,3,4,5,9,10,11] t6 b7
  have b8 : a 29 ≠ 10 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 10 t3 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,2,3,4,5,11] := remove (a 29) 10 [0,1,2,3,4,5,10,11] t7 b8
  have b9 : a 29 ≠ 11 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 11 t3 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,2,3,4,5] := remove (a 29) 11 [0,1,2,3,4,5,11] t8 b9
  have b10 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,3] := remove (a 30) 1 [0,1,2,3] d30 b10
  have b11 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,3] := remove (a 30) 2 [0,2,3] t10 b11
  have b12 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0] := remove (a 30) 3 [0,3] t11 b12
  have b13 : a 31 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 1 t2 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d31 b13
  have b14 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 t2 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 t2 c47 (by decide +kernel)
  have t15 : a 31 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t3 (And.intro t9 (And.intro t12 (t15)))))

theorem chunk7 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d18 : a 18 ∈ [0,1,14,15])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    : a 31 ∈ [0,6] ∧ a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d31 b0
  have b1 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 31 ≠ 7 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,6,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 7 [0,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 31 ≠ 8 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 8 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,6,9,10,11,12,13,14,15,16,17] := remove (a 31) 8 [0,6,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 31 ≠ 9 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,6,10,11,12,13,14,15,16,17] := remove (a 31) 9 [0,6,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 31 ≠ 10 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,6,11,12,13,14,15,16,17] := remove (a 31) 10 [0,6,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 31 ≠ 11 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,6,12,13,14,15,16,17] := remove (a 31) 11 [0,6,11,12,13,14,15,16,17] t5 b6
  have b7 : a 31 ≠ 12 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 12 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,6,13,14,15,16,17] := remove (a 31) 12 [0,6,12,13,14,15,16,17] t6 b7
  have b8 : a 31 ≠ 13 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 13 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,6,14,15,16,17] := remove (a 31) 13 [0,6,13,14,15,16,17] t7 b8
  have b9 : a 31 ≠ 14 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 14 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0,6,15,16,17] := remove (a 31) 14 [0,6,14,15,16,17] t8 b9
  have b10 : a 31 ≠ 15 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 15 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,6,16,17] := remove (a 31) 15 [0,6,15,16,17] t9 b10
  have b11 : a 31 ≠ 16 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 16 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,6,17] := remove (a 31) 16 [0,6,16,17] t10 b11
  have b12 : a 31 ≠ 17 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 17 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,6] := remove (a 31) 17 [0,6,17] t11 b12
  have b13 : a 16 ≠ 2 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 2 d18 c49 (by decide +kernel)
  have t13 : a 16 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d16 b13
  have b14 : a 16 ≠ 3 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 3 d18 c49 (by decide +kernel)
  have t14 : a 16 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 16 ≠ 4 := exclude [0,1,14,15] (edge r49) (a 16) (a 18) 4 d18 c49 (by decide +kernel)
  have t15 : a 16 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 16) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t12 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_179
