import PartitionData205_212
namespace PartitionCover205_212
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23])
    (d11 : a 11 ∈ [0,12])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0])
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 27 ∈ [0,1,12,13] ∧ a 28 ∈ [0,2,8,9,10,11] := by
  have b0 : a 27 ≠ 14 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 14 d11 c39 (by decide +kernel)
  have t0 : a 27 ∈ [0,1,12,13,15,16,17,18,19,20,21,22,23] := remove (a 27) 14 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] d27 b0
  have b1 : a 27 ≠ 15 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 15 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,12,13,16,17,18,19,20,21,22,23] := remove (a 27) 15 [0,1,12,13,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 27 ≠ 16 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 16 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1,12,13,17,18,19,20,21,22,23] := remove (a 27) 16 [0,1,12,13,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 27 ≠ 17 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 17 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,12,13,18,19,20,21,22,23] := remove (a 27) 17 [0,1,12,13,17,18,19,20,21,22,23] t2 b3
  have b4 : a 27 ≠ 18 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 18 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,1,12,13,19,20,21,22,23] := remove (a 27) 18 [0,1,12,13,18,19,20,21,22,23] t3 b4
  have b5 : a 27 ≠ 19 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 19 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,12,13,20,21,22,23] := remove (a 27) 19 [0,1,12,13,19,20,21,22,23] t4 b5
  have b6 : a 27 ≠ 20 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 20 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,1,12,13,21,22,23] := remove (a 27) 20 [0,1,12,13,20,21,22,23] t5 b6
  have b7 : a 27 ≠ 21 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 21 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,12,13,22,23] := remove (a 27) 21 [0,1,12,13,21,22,23] t6 b7
  have b8 : a 27 ≠ 22 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 22 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,1,12,13,23] := remove (a 27) 22 [0,1,12,13,22,23] t7 b8
  have b9 : a 27 ≠ 23 := exclude [0,12] (fun u v => edge r39 v u) (a 27) (a 11) 23 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1,12,13] := remove (a 27) 23 [0,1,12,13,23] t8 b9
  have b10 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d28 b10
  have b11 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 28) 3 [0,2,3,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 28) 4 [0,2,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,2,6,7,8,9,10,11] := remove (a 28) 5 [0,2,5,6,7,8,9,10,11] t12 b13
  have b14 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,7,8,9,10,11] := remove (a 28) 6 [0,2,6,7,8,9,10,11] t13 b14
  have b15 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,8,9,10,11] := remove (a 28) 7 [0,2,7,8,9,10,11] t14 b15
  exact And.intro t9 (t15)

theorem chunk17 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,8,9,10,11])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 28 ∈ [0,2] ∧ a 29 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 28 ≠ 8 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,9,10,11] := remove (a 28) 8 [0,2,8,9,10,11] d28 b0
  have b1 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,10,11] := remove (a 28) 9 [0,2,9,10,11] t0 b1
  have b2 : a 28 ≠ 10 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,11] := remove (a 28) 10 [0,2,10,11] t1 b2
  have b3 : a 28 ≠ 11 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2] := remove (a 28) 11 [0,2,11] t2 b3
  have b4 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d29 b4
  have b5 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 29 ≠ 7 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 8 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 29 ≠ 9 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 9 [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 29 ≠ 10 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 10 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 10 [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 29 ≠ 11 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 11 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 11 [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 29 ≠ 12 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 12 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,1,13,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 12 [0,1,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 29 ≠ 13 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 13 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,14,15,16,17,18,19,20,21,22,23] := remove (a 29) 13 [0,1,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t3 (t15)

theorem chunk18 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,14,15,16,17,18,19,20,21,22,23])
    (d13 : a 13 ∈ [0])
    (d14 : a 14 ∈ [0,2])
    (d15 : a 15 ∈ [0,6])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,1] ∧ a 14 ∈ [0] ∧ a 30 ∈ [0,1,7,8,9,10,11] := by
  have b0 : a 29 ≠ 14 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 14 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,15,16,17,18,19,20,21,22,23] := remove (a 29) 14 [0,1,14,15,16,17,18,19,20,21,22,23] d29 b0
  have b1 : a 29 ≠ 15 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 15 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,16,17,18,19,20,21,22,23] := remove (a 29) 15 [0,1,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 29 ≠ 16 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 16 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,17,18,19,20,21,22,23] := remove (a 29) 16 [0,1,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 29 ≠ 17 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 17 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,18,19,20,21,22,23] := remove (a 29) 17 [0,1,17,18,19,20,21,22,23] t2 b3
  have b4 : a 29 ≠ 18 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,19,20,21,22,23] := remove (a 29) 18 [0,1,18,19,20,21,22,23] t3 b4
  have b5 : a 29 ≠ 19 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 19 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,20,21,22,23] := remove (a 29) 19 [0,1,19,20,21,22,23] t4 b5
  have b6 : a 29 ≠ 20 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 20 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,21,22,23] := remove (a 29) 20 [0,1,20,21,22,23] t5 b6
  have b7 : a 29 ≠ 21 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 21 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,22,23] := remove (a 29) 21 [0,1,21,22,23] t6 b7
  have b8 : a 29 ≠ 22 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 22 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1,23] := remove (a 29) 22 [0,1,22,23] t7 b8
  have b9 : a 29 ≠ 23 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 23 d13 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0,1] := remove (a 29) 23 [0,1,23] t8 b9
  have b10 : a 14 ≠ 2 := exclude [0,6] (edge r45) (a 14) (a 15) 2 d15 c45 (by decide +kernel)
  have t10 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b10
  have b11 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 t10 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 30) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b11
  have b12 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 t10 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,1,3,4,5,6,7,8,9,10,11] t11 b12
  have b13 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 t10 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 30) 4 [0,1,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 t10 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,6,7,8,9,10,11] := remove (a 30) 5 [0,1,5,6,7,8,9,10,11] t13 b14
  have b15 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 t10 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,7,8,9,10,11] := remove (a 30) 6 [0,1,6,7,8,9,10,11] t14 b15
  exact And.intro t9 (And.intro t10 (t15))

theorem chunk19 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,7,8,9,10,11])
    (d14 : a 14 ∈ [0])
    (d16 : a 16 ∈ [0,1,6,7])
    (d20 : a 20 ∈ [0,1,2,6,7,8,9,10,11])
    (d24 : a 24 ∈ [0,12])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d17 : a 17 ∈ [0,6])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 30 ∈ [0,1] ∧ a 16 ∈ [0] ∧ a 20 ∈ [0,1] ∧ a 21 ∈ [0,2,3,4,5] := by
  have b0 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,8,9,10,11] := remove (a 30) 7 [0,1,7,8,9,10,11] d30 b0
  have b1 : a 30 ≠ 8 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,9,10,11] := remove (a 30) 8 [0,1,8,9,10,11] t0 b1
  have b2 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,10,11] := remove (a 30) 9 [0,1,9,10,11] t1 b2
  have b3 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,11] := remove (a 30) 10 [0,1,10,11] t2 b3
  have b4 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1] := remove (a 30) 11 [0,1,11] t3 b4
  have b5 : a 16 ≠ 6 := exclude [0,1,2,6,7,8,9,10,11] (edge r50) (a 16) (a 20) 6 d20 c50 (by decide +kernel)
  have t5 : a 16 ∈ [0,1,7] := remove (a 16) 6 [0,1,6,7] d16 b5
  have b6 : a 16 ≠ 7 := exclude [0,1,2,6,7,8,9,10,11] (edge r50) (a 16) (a 20) 7 d20 c50 (by decide +kernel)
  have t6 : a 16 ∈ [0,1] := remove (a 16) 7 [0,1,7] t5 b6
  have b7 : a 20 ≠ 2 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 2 t6 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,6,7,8,9,10,11] := remove (a 20) 2 [0,1,2,6,7,8,9,10,11] d20 b7
  have b8 : a 20 ≠ 6 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 6 t6 c50 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,7,8,9,10,11] := remove (a 20) 6 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 20 ≠ 7 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 7 t6 c50 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,8,9,10,11] := remove (a 20) 7 [0,1,7,8,9,10,11] t8 b9
  have b10 : a 20 ≠ 8 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 8 t6 c50 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,9,10,11] := remove (a 20) 8 [0,1,8,9,10,11] t9 b10
  have b11 : a 20 ≠ 9 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 9 t6 c50 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,10,11] := remove (a 20) 9 [0,1,9,10,11] t10 b11
  have b12 : a 20 ≠ 10 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 10 t6 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,1,11] := remove (a 20) 10 [0,1,10,11] t11 b12
  have b13 : a 20 ≠ 11 := exclude [0,1] (fun u v => edge r50 v u) (a 20) (a 16) 11 t6 c50 (by decide +kernel)
  have t13 : a 20 ∈ [0,1] := remove (a 20) 11 [0,1,11] t12 b13
  have b14 : a 16 ≠ 1 := exclude [0,12] (edge r51) (a 16) (a 24) 1 d24 c51 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 1 [0,1] t6 b14
  have b15 : a 21 ≠ 1 := exclude [0,6] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t15 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b15
  exact And.intro t4 (And.intro t14 (And.intro t13 (t15)))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_212
