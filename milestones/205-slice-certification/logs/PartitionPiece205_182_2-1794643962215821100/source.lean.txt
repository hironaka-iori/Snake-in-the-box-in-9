import PartitionData205_182
namespace PartitionCover205_182
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,2,3,4,5])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d11 : a 11 ∈ [0,2])
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 13 ∈ [0,2,3,5] ∧ a 25 ∈ [0,1,2,3,4,5] ∧ a 26 ∈ [0,1,2,3,5,6,8] ∧ a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 13 ≠ 4 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t0 : a 13 ∈ [0,2,3,5] := remove (a 13) 4 [0,2,3,4,5] d13 b0
  have b1 : a 25 ≠ 6 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d25 b1
  have b2 : a 25 ≠ 7 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 25) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 25 ≠ 8 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] := remove (a 25) 8 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 25 ≠ 9 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,2,3,4,5,10,11,12,13,14,15,16,17] := remove (a 25) 9 [0,1,2,3,4,5,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 25 ≠ 10 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,2,3,4,5,11,12,13,14,15,16,17] := remove (a 25) 10 [0,1,2,3,4,5,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 25 ≠ 11 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,2,3,4,5,12,13,14,15,16,17] := remove (a 25) 11 [0,1,2,3,4,5,11,12,13,14,15,16,17] t5 b6
  have b7 : a 25 ≠ 12 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 12 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,2,3,4,5,13,14,15,16,17] := remove (a 25) 12 [0,1,2,3,4,5,12,13,14,15,16,17] t6 b7
  have b8 : a 25 ≠ 13 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 13 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,2,3,4,5,14,15,16,17] := remove (a 25) 13 [0,1,2,3,4,5,13,14,15,16,17] t7 b8
  have b9 : a 25 ≠ 14 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 14 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,2,3,4,5,15,16,17] := remove (a 25) 14 [0,1,2,3,4,5,14,15,16,17] t8 b9
  have b10 : a 25 ≠ 15 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 15 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,2,3,4,5,16,17] := remove (a 25) 15 [0,1,2,3,4,5,15,16,17] t9 b10
  have b11 : a 25 ≠ 16 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 16 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,2,3,4,5,17] := remove (a 25) 16 [0,1,2,3,4,5,16,17] t10 b11
  have b12 : a 25 ≠ 17 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 17 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,2,3,4,5] := remove (a 25) 17 [0,1,2,3,4,5,17] t11 b12
  have b13 : a 26 ≠ 4 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 4 d10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,1,2,3,5,6,7,8] := remove (a 26) 4 [0,1,2,3,4,5,6,7,8] d26 b13
  have b14 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,2,3,5,6,8] := remove (a 26) 7 [0,1,2,3,5,6,7,8] t13 b14
  have b15 : a 27 ≠ 2 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d27 b15
  exact And.intro t0 (And.intro t12 (And.intro t14 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d11 : a 11 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0,1])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 27 ∈ [0,1] ∧ a 28 ∈ [0,1,2,3,5,6,7,8] := by
  have b0 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d27 b0
  have b1 : a 27 ≠ 4 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 27 ≠ 6 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 6 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 27 ≠ 7 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,8,9,10,11,12,13,14,15,16,17] := remove (a 27) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17] t3 b4
  have b5 : a 27 ≠ 8 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,9,10,11,12,13,14,15,16,17] := remove (a 27) 8 [0,1,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 27 ≠ 9 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,10,11,12,13,14,15,16,17] := remove (a 27) 9 [0,1,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 27 ≠ 10 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 10 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,11,12,13,14,15,16,17] := remove (a 27) 10 [0,1,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 27 ≠ 11 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 11 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,12,13,14,15,16,17] := remove (a 27) 11 [0,1,11,12,13,14,15,16,17] t7 b8
  have b9 : a 27 ≠ 12 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 12 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,13,14,15,16,17] := remove (a 27) 12 [0,1,12,13,14,15,16,17] t8 b9
  have b10 : a 27 ≠ 13 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 13 d11 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0,1,14,15,16,17] := remove (a 27) 13 [0,1,13,14,15,16,17] t9 b10
  have b11 : a 27 ≠ 14 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 14 d11 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,1,15,16,17] := remove (a 27) 14 [0,1,14,15,16,17] t10 b11
  have b12 : a 27 ≠ 15 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 15 d11 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,16,17] := remove (a 27) 15 [0,1,15,16,17] t11 b12
  have b13 : a 27 ≠ 16 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 16 d11 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,17] := remove (a 27) 16 [0,1,16,17] t12 b13
  have b14 : a 27 ≠ 17 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 17 d11 c39 (by decide +kernel)
  have t14 : a 27 ∈ [0,1] := remove (a 27) 17 [0,1,17] t13 b14
  have b15 : a 28 ≠ 4 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,1,2,3,5,6,7,8] := remove (a 28) 4 [0,1,2,3,4,5,6,7,8] d28 b15
  exact And.intro t14 (t15)

theorem chunk10 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,2,3,5,6,7,8])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d13 : a 13 ∈ [0,2,3,5])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d14 : a 14 ∈ [0])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 28 ∈ [0,1,2,3,5,6,8] ∧ a 29 ∈ [0,1,4,5,6,7,9] ∧ a 30 ∈ [0,2,6,8,12,14,16,17] := by
  have b0 : a 28 ≠ 7 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,1,2,3,5,6,8] := remove (a 28) 7 [0,1,2,3,5,6,7,8] d28 b0
  have b1 : a 29 ≠ 2 := exclude [0,2,3,5] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d29 b1
  have b2 : a 29 ≠ 3 := exclude [0,2,3,5] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 29 ≠ 8 := exclude [0,2,3,5] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,4,5,6,7,9,10,11] := remove (a 29) 8 [0,1,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 29 ≠ 10 := exclude [0,2,3,5] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,4,5,6,7,9,11] := remove (a 29) 10 [0,1,4,5,6,7,9,10,11] t3 b4
  have b5 : a 29 ≠ 11 := exclude [0,2,3,5] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,4,5,6,7,9] := remove (a 29) 11 [0,1,4,5,6,7,9,11] t4 b5
  have b6 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d30 b6
  have b7 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 7 [0,2,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,6,8,10,11,12,13,14,15,16,17] := remove (a 30) 9 [0,2,6,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,6,8,11,12,13,14,15,16,17] := remove (a 30) 10 [0,2,6,8,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,6,8,12,13,14,15,16,17] := remove (a 30) 11 [0,2,6,8,11,12,13,14,15,16,17] t12 b13
  have b14 : a 30 ≠ 13 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,2,6,8,12,14,15,16,17] := remove (a 30) 13 [0,2,6,8,12,13,14,15,16,17] t13 b14
  have b15 : a 30 ≠ 15 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,6,8,12,14,16,17] := remove (a 30) 15 [0,2,6,8,12,14,15,16,17] t14 b15
  exact And.intro t0 (And.intro t5 (t15))

theorem chunk11 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,6,8,12,14,16,17])
    (d14 : a 14 ∈ [0])
    (d17 : a 17 ∈ [0,1,6,7,12,13])
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3,5,6,8])
    (d24 : a 24 ∈ [0,1,4])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    : a 30 ∈ [0,2,6,8,12,14] ∧ a 17 ∈ [0,1] ∧ a 20 ∈ [0,1] ∧ a 24 ∈ [0,4] ∧ a 25 ∈ [0,1] := by
  have b0 : a 30 ≠ 16 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,6,8,12,14,17] := remove (a 30) 16 [0,2,6,8,12,14,16,17] d30 b0
  have b1 : a 30 ≠ 17 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,6,8,12,14] := remove (a 30) 17 [0,2,6,8,12,14,17] t0 b1
  have b2 : a 17 ≠ 6 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 6 d16 c48 (by decide +kernel)
  have t2 : a 17 ∈ [0,1,7,12,13] := remove (a 17) 6 [0,1,6,7,12,13] d17 b2
  have b3 : a 17 ≠ 7 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 7 d16 c48 (by decide +kernel)
  have t3 : a 17 ∈ [0,1,12,13] := remove (a 17) 7 [0,1,7,12,13] t2 b3
  have b4 : a 17 ≠ 12 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 12 d16 c48 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,13] := remove (a 17) 12 [0,1,12,13] t3 b4
  have b5 : a 17 ≠ 13 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 13 d16 c48 (by decide +kernel)
  have t5 : a 17 ∈ [0,1] := remove (a 17) 13 [0,1,13] t4 b5
  have b6 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 2 d16 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,3,5,6,8] := remove (a 20) 2 [0,1,2,3,5,6,8] d20 b6
  have b7 : a 20 ≠ 3 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 3 d16 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,5,6,8] := remove (a 20) 3 [0,1,3,5,6,8] t6 b7
  have b8 : a 20 ≠ 5 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 5 d16 c50 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,6,8] := remove (a 20) 5 [0,1,5,6,8] t7 b8
  have b9 : a 20 ≠ 6 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 6 d16 c50 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,8] := remove (a 20) 6 [0,1,6,8] t8 b9
  have b10 : a 20 ≠ 8 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 8 d16 c50 (by decide +kernel)
  have t10 : a 20 ∈ [0,1] := remove (a 20) 8 [0,1,8] t9 b10
  have b11 : a 24 ≠ 1 := exclude [0,1] (fun u v => edge r51 v u) (a 24) (a 16) 1 d16 c51 (by decide +kernel)
  have t11 : a 24 ∈ [0,4] := remove (a 24) 1 [0,1,4] d24 b11
  have b12 : a 25 ≠ 2 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 2 t5 c54 (by decide +kernel)
  have t12 : a 25 ∈ [0,1,3,4,5] := remove (a 25) 2 [0,1,2,3,4,5] d25 b12
  have b13 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 3 t5 c54 (by decide +kernel)
  have t13 : a 25 ∈ [0,1,4,5] := remove (a 25) 3 [0,1,3,4,5] t12 b13
  have b14 : a 25 ≠ 4 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 4 t5 c54 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,5] := remove (a 25) 4 [0,1,4,5] t13 b14
  have b15 : a 25 ≠ 5 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 5 t5 c54 (by decide +kernel)
  have t15 : a 25 ∈ [0,1] := remove (a 25) 5 [0,1,5] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t10 (And.intro t11 (t15))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_182
