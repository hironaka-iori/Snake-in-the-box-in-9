import PartitionData205_198
namespace PartitionCover205_198
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    : a 14 ∈ [0] ∧ a 22 ∈ [0,3] ∧ a 15 ∈ [0,1,3,6] ∧ a 9 ∈ [0,1,2,4] ∧ a 10 ∈ [0,2,3] := by
  have b0 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b0
  have b1 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,3,4,5,6,7,8] := remove (a 22) 1 [0,1,2,3,4,5,6,7,8] d22 b1
  have b2 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t2 : a 22 ∈ [0,3,4,5,6,7,8] := remove (a 22) 2 [0,2,3,4,5,6,7,8] t1 b2
  have b3 : a 22 ≠ 4 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t3 : a 22 ∈ [0,3,5,6,7,8] := remove (a 22) 4 [0,3,4,5,6,7,8] t2 b3
  have b4 : a 22 ≠ 5 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t4 : a 22 ∈ [0,3,6,7,8] := remove (a 22) 5 [0,3,5,6,7,8] t3 b4
  have b5 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,3,7,8] := remove (a 22) 6 [0,3,6,7,8] t4 b5
  have b6 : a 22 ≠ 7 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,3,8] := remove (a 22) 7 [0,3,7,8] t5 b6
  have b7 : a 22 ≠ 8 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,3] := remove (a 22) 8 [0,3,8] t6 b7
  have b8 : a 15 ≠ 2 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,3,4,5,6,7,8] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8] d15 b8
  have b9 : a 15 ≠ 4 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 4 d7 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,3,5,6,7,8] := remove (a 15) 4 [0,1,3,4,5,6,7,8] t8 b9
  have b10 : a 15 ≠ 5 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 5 d7 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,3,6,7,8] := remove (a 15) 5 [0,1,3,5,6,7,8] t9 b10
  have b11 : a 15 ≠ 7 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t11 : a 15 ∈ [0,1,3,6,8] := remove (a 15) 7 [0,1,3,6,7,8] t10 b11
  have b12 : a 15 ≠ 8 := exclude [0,1] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,3,6] := remove (a 15) 8 [0,1,3,6,8] t11 b12
  have b13 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 3 d8 c28 (by decide +kernel)
  have t13 : a 9 ∈ [0,1,2,4,5] := remove (a 9) 3 [0,1,2,3,4,5] d9 b13
  have b14 : a 9 ≠ 5 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t14 : a 9 ∈ [0,1,2,4] := remove (a 9) 5 [0,1,2,4,5] t13 b14
  have b15 : a 10 ≠ 1 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 1 d8 c29 (by decide +kernel)
  have t15 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b15
  exact And.intro t0 (And.intro t7 (And.intro t12 (And.intro t14 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,2,3])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0,1,2,4])
    (d11 : a 11 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,4,5,8,9,10,11])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 10 ∈ [0,2] ∧ a 9 ∈ [0,1] ∧ a 13 ∈ [0,1,4,5] ∧ a 25 ∈ [0,1] ∧ a 26 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t0 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] d10 b0
  have b1 : a 9 ≠ 2 := exclude [0,1] (edge r32) (a 9) (a 11) 2 d11 c32 (by decide +kernel)
  have t1 : a 9 ∈ [0,1,4] := remove (a 9) 2 [0,1,2,4] d9 b1
  have b2 : a 9 ≠ 4 := exclude [0,1] (edge r32) (a 9) (a 11) 4 d11 c32 (by decide +kernel)
  have t2 : a 9 ∈ [0,1] := remove (a 9) 4 [0,1,4] t1 b2
  have b3 : a 13 ≠ 8 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 8 t2 c33 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,4,5,9,10,11] := remove (a 13) 8 [0,1,4,5,8,9,10,11] d13 b3
  have b4 : a 13 ≠ 9 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 9 t2 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,4,5,10,11] := remove (a 13) 9 [0,1,4,5,9,10,11] t3 b4
  have b5 : a 13 ≠ 10 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 10 t2 c33 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,4,5,11] := remove (a 13) 10 [0,1,4,5,10,11] t4 b5
  have b6 : a 13 ≠ 11 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 11 t2 c33 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,4,5] := remove (a 13) 11 [0,1,4,5,11] t5 b6
  have b7 : a 25 ≠ 2 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 2 t2 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,3,4,5] := remove (a 25) 2 [0,1,2,3,4,5] d25 b7
  have b8 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 3 t2 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,4,5] := remove (a 25) 3 [0,1,3,4,5] t7 b8
  have b9 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 4 t2 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,5] := remove (a 25) 4 [0,1,4,5] t8 b9
  have b10 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 5 t2 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1] := remove (a 25) 5 [0,1,5] t9 b10
  have b11 : a 26 ≠ 2 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 2 t0 c37 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d26 b11
  have b12 : a 26 ≠ 3 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 3 t0 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 26 ≠ 6 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 6 t0 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 t0 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 26) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 26 ≠ 8 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 8 t0 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17] := remove (a 26) 8 [0,1,4,5,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t6 (And.intro t10 (t15))))

theorem chunk6 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,4,5,9,10,11,12,13,14,15,16,17])
    (d10 : a 10 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,3,6])
    (d11 : a 11 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2])
    (d28 : a 28 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d13 : a 13 ∈ [0,1,4,5])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 26 ∈ [0,1,4,5] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,1] ∧ a 28 ∈ [0,2,3] ∧ a 29 ∈ [0,1,5,6,7,8,9] := by
  have b0 : a 26 ≠ 9 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 9 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,1,4,5,10,11,12,13,14,15,16,17] := remove (a 26) 9 [0,1,4,5,9,10,11,12,13,14,15,16,17] d26 b0
  have b1 : a 26 ≠ 10 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 10 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,4,5,11,12,13,14,15,16,17] := remove (a 26) 10 [0,1,4,5,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 26 ≠ 11 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 11 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,4,5,12,13,14,15,16,17] := remove (a 26) 11 [0,1,4,5,11,12,13,14,15,16,17] t1 b2
  have b3 : a 26 ≠ 12 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 12 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,4,5,13,14,15,16,17] := remove (a 26) 12 [0,1,4,5,12,13,14,15,16,17] t2 b3
  have b4 : a 26 ≠ 13 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 13 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,4,5,14,15,16,17] := remove (a 26) 13 [0,1,4,5,13,14,15,16,17] t3 b4
  have b5 : a 26 ≠ 14 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 14 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,4,5,15,16,17] := remove (a 26) 14 [0,1,4,5,14,15,16,17] t4 b5
  have b6 : a 26 ≠ 15 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 15 d10 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1,4,5,16,17] := remove (a 26) 15 [0,1,4,5,15,16,17] t5 b6
  have b7 : a 26 ≠ 16 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 16 d10 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,1,4,5,17] := remove (a 26) 16 [0,1,4,5,16,17] t6 b7
  have b8 : a 26 ≠ 17 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 17 d10 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,1,4,5] := remove (a 26) 17 [0,1,4,5,17] t7 b8
  have b9 : a 15 ≠ 3 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,6] := remove (a 15) 3 [0,1,3,6] d15 b9
  have b10 : a 15 ≠ 6 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 6 d11 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0,1] := remove (a 15) 6 [0,1,6] t9 b10
  have b11 : a 27 ≠ 2 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1] := remove (a 27) 2 [0,1,2] d27 b11
  have b12 : a 28 ≠ 1 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b12
  have b13 : a 29 ≠ 2 := exclude [0,1,4,5] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0,1,4,5] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,4,5,6,7,8,9] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9] t13 b14
  have b15 : a 29 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,5,6,7,8,9] := remove (a 29) 4 [0,1,4,5,6,7,8,9] t14 b15
  exact And.intro t8 (And.intro t10 (And.intro t11 (And.intro t12 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,5,6,7,8,9])
    (d13 : a 13 ∈ [0,1,4,5])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [0,5,6,11])
    (d16 : a 16 ∈ [0,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    : a 29 ∈ [0,1,6,7] ∧ a 31 ∈ [0,1,6,8,9,11] ∧ a 17 ∈ [0,6] ∧ a 24 ∈ [0,1,6,7,9,10,11] := by
  have b0 : a 29 ≠ 5 := exclude [0,1,4,5] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,6,7,8,9] := remove (a 29) 5 [0,1,5,6,7,8,9] d29 b0
  have b1 : a 29 ≠ 8 := exclude [0,1,4,5] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,6,7,9] := remove (a 29) 8 [0,1,6,7,8,9] t0 b1
  have b2 : a 29 ≠ 9 := exclude [0,1,4,5] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,6,7] := remove (a 29) 9 [0,1,6,7,9] t1 b2
  have b3 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 31) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d31 b3
  have b4 : a 31 ≠ 3 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 31) 3 [0,1,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 31 ≠ 4 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 31) 4 [0,1,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0,1,6,7,8,9,10,11] := remove (a 31) 5 [0,1,5,6,7,8,9,10,11] t5 b6
  have b7 : a 31 ≠ 7 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 7 d15 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,6,8,9,10,11] := remove (a 31) 7 [0,1,6,7,8,9,10,11] t6 b7
  have b8 : a 31 ≠ 10 := exclude [0,1] (fun u v => edge r47 v u) (a 31) (a 15) 10 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,6,8,9,11] := remove (a 31) 10 [0,1,6,8,9,10,11] t7 b8
  have b9 : a 17 ≠ 5 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 5 d16 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0,6,11] := remove (a 17) 5 [0,5,6,11] d17 b9
  have b10 : a 17 ≠ 11 := exclude [0,3] (fun u v => edge r48 v u) (a 17) (a 16) 11 d16 c48 (by decide +kernel)
  have t10 : a 17 ∈ [0,6] := remove (a 17) 11 [0,6,11] t9 b10
  have b11 : a 24 ≠ 2 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 2 d16 c51 (by decide +kernel)
  have t11 : a 24 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 24) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d24 b11
  have b12 : a 24 ≠ 3 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 3 d16 c51 (by decide +kernel)
  have t12 : a 24 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 24) 3 [0,1,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 24 ≠ 4 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 4 d16 c51 (by decide +kernel)
  have t13 : a 24 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 24) 4 [0,1,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 24 ≠ 5 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 5 d16 c51 (by decide +kernel)
  have t14 : a 24 ∈ [0,1,6,7,8,9,10,11] := remove (a 24) 5 [0,1,5,6,7,8,9,10,11] t13 b14
  have b15 : a 24 ≠ 8 := exclude [0,3] (fun u v => edge r51 v u) (a 24) (a 16) 8 d16 c51 (by decide +kernel)
  have t15 : a 24 ∈ [0,1,6,7,9,10,11] := remove (a 24) 8 [0,1,6,7,8,9,10,11] t14 b15
  exact And.intro t2 (And.intro t8 (And.intro t10 (t15)))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_198
