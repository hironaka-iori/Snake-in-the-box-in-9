import PartitionData205_213
namespace PartitionCover205_213
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,16,17])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5,6,7,8])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d14 : a 14 ∈ [0])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 28 ∈ [0,1] ∧ a 29 ∈ [0,1] ∧ a 30 ∈ [0,8,9,10,11,12,13,14,15,16,17] := by
  have b0 : a 28 ≠ 16 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 16 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,1,17] := remove (a 28) 16 [0,1,16,17] d28 b0
  have b1 : a 28 ≠ 17 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 17 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,1] := remove (a 28) 17 [0,1,17] t0 b1
  have b2 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1,3,4,5,6,7,8] := remove (a 29) 2 [0,1,2,3,4,5,6,7,8] d29 b2
  have b3 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,4,5,6,7,8] := remove (a 29) 3 [0,1,3,4,5,6,7,8] t2 b3
  have b4 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,1,5,6,7,8] := remove (a 29) 4 [0,1,4,5,6,7,8] t3 b4
  have b5 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,1,6,7,8] := remove (a 29) 5 [0,1,5,6,7,8] t4 b5
  have b6 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0,1,7,8] := remove (a 29) 6 [0,1,6,7,8] t5 b6
  have b7 : a 29 ≠ 7 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 7 d13 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0,1,8] := remove (a 29) 7 [0,1,7,8] t6 b7
  have b8 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t8 : a 29 ∈ [0,1] := remove (a 29) 8 [0,1,8] t7 b8
  have b9 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d30 b9
  have b10 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17] t13 b14
  have b15 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 7 [0,7,8,9,10,11,12,13,14,15,16,17] t14 b15
  exact And.intro t1 (And.intro t8 (t15))

theorem chunk17 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,8,9,10,11,12,13,14,15,16,17])
    (d14 : a 14 ∈ [0])
    (d16 : a 16 ∈ [0,8,12,18])
    (d20 : a 20 ∈ [0,1,6,7,8])
    (d24 : a 24 ∈ [0,4])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    : a 30 ∈ [0] ∧ a 16 ∈ [0] ∧ a 20 ∈ [0,6] := by
  have b0 : a 30 ≠ 8 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,9,10,11,12,13,14,15,16,17] := remove (a 30) 8 [0,8,9,10,11,12,13,14,15,16,17] d30 b0
  have b1 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,10,11,12,13,14,15,16,17] := remove (a 30) 9 [0,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,11,12,13,14,15,16,17] := remove (a 30) 10 [0,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,12,13,14,15,16,17] := remove (a 30) 11 [0,11,12,13,14,15,16,17] t2 b3
  have b4 : a 30 ≠ 12 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,13,14,15,16,17] := remove (a 30) 12 [0,12,13,14,15,16,17] t3 b4
  have b5 : a 30 ≠ 13 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,14,15,16,17] := remove (a 30) 13 [0,13,14,15,16,17] t4 b5
  have b6 : a 30 ≠ 14 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,15,16,17] := remove (a 30) 14 [0,14,15,16,17] t5 b6
  have b7 : a 30 ≠ 15 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,16,17] := remove (a 30) 15 [0,15,16,17] t6 b7
  have b8 : a 30 ≠ 16 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,17] := remove (a 30) 16 [0,16,17] t7 b8
  have b9 : a 30 ≠ 17 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0] := remove (a 30) 17 [0,17] t8 b9
  have b10 : a 16 ≠ 8 := exclude [0,1,6,7,8] (edge r50) (a 16) (a 20) 8 d20 c50 (by decide +kernel)
  have t10 : a 16 ∈ [0,12,18] := remove (a 16) 8 [0,8,12,18] d16 b10
  have b11 : a 16 ≠ 18 := exclude [0,1,6,7,8] (edge r50) (a 16) (a 20) 18 d20 c50 (by decide +kernel)
  have t11 : a 16 ∈ [0,12] := remove (a 16) 18 [0,12,18] t10 b11
  have b12 : a 20 ≠ 1 := exclude [0,12] (fun u v => edge r50 v u) (a 20) (a 16) 1 t11 c50 (by decide +kernel)
  have t12 : a 20 ∈ [0,6,7,8] := remove (a 20) 1 [0,1,6,7,8] d20 b12
  have b13 : a 20 ≠ 7 := exclude [0,12] (fun u v => edge r50 v u) (a 20) (a 16) 7 t11 c50 (by decide +kernel)
  have t13 : a 20 ∈ [0,6,8] := remove (a 20) 7 [0,6,7,8] t12 b13
  have b14 : a 20 ≠ 8 := exclude [0,12] (fun u v => edge r50 v u) (a 20) (a 16) 8 t11 c50 (by decide +kernel)
  have t14 : a 20 ∈ [0,6] := remove (a 20) 8 [0,6,8] t13 b14
  have b15 : a 16 ≠ 12 := exclude [0,4] (edge r51) (a 16) (a 24) 12 d24 c51 (by decide +kernel)
  have t15 : a 16 ∈ [0] := remove (a 16) 12 [0,12] t11 b15
  exact And.intro t9 (And.intro t15 (t14))

theorem chunk18 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,2])
    (d21 : a 21 ∈ [0,4])
    (d25 : a 25 ∈ [0,2,7,10,12,14])
    (d23 : a 23 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d20 : a 20 ∈ [0,6])
    (d22 : a 22 ∈ [0,1,2,9,10,11])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d30 : a 30 ∈ [0])
    (d26 : a 26 ∈ [0,2,3,5])
    (d24 : a 24 ∈ [0,4])
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    : a 17 ∈ [0] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0,2] ∧ a 23 ∈ [0] ∧ a 19 ∈ [0] ∧ a 20 ∈ [0] ∧ a 22 ∈ [0,10] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 26 ∈ [0,2,5] := by
  have b0 : a 17 ≠ 2 := exclude [0,4] (edge r53) (a 17) (a 21) 2 d21 c53 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b0
  have b1 : a 21 ≠ 4 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 4 t0 c53 (by decide +kernel)
  have t1 : a 21 ∈ [0] := remove (a 21) 4 [0,4] d21 b1
  have b2 : a 25 ≠ 7 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 7 t0 c54 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,10,12,14] := remove (a 25) 7 [0,2,7,10,12,14] d25 b2
  have b3 : a 25 ≠ 10 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 10 t0 c54 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,12,14] := remove (a 25) 10 [0,2,10,12,14] t2 b3
  have b4 : a 25 ≠ 12 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 12 t0 c54 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,14] := remove (a 25) 12 [0,2,12,14] t3 b4
  have b5 : a 25 ≠ 14 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 14 t0 c54 (by decide +kernel)
  have t5 : a 25 ∈ [0,2] := remove (a 25) 14 [0,2,14] t4 b5
  have b6 : a 23 ≠ 1 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b6
  have b7 : a 19 ≠ 1 := exclude [0] (edge r59) (a 19) (a 27) 1 d27 c59 (by decide +kernel)
  have t7 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b7
  have b8 : a 20 ≠ 6 := exclude [0] (edge r60) (a 20) (a 21) 6 t1 c60 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 6 [0,6] d20 b8
  have b9 : a 22 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 1 t8 c61 (by decide +kernel)
  have t9 : a 22 ∈ [0,2,9,10,11] := remove (a 22) 1 [0,1,2,9,10,11] d22 b9
  have b10 : a 28 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 1 t8 c62 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b10
  have b11 : a 29 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 1 t1 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b11
  have b12 : a 22 ≠ 2 := exclude [0] (edge r66) (a 22) (a 30) 2 d30 c66 (by decide +kernel)
  have t12 : a 22 ∈ [0,9,10,11] := remove (a 22) 2 [0,2,9,10,11] t9 b12
  have b13 : a 22 ≠ 9 := exclude [0] (edge r66) (a 22) (a 30) 9 d30 c66 (by decide +kernel)
  have t13 : a 22 ∈ [0,10,11] := remove (a 22) 9 [0,9,10,11] t12 b13
  have b14 : a 22 ≠ 11 := exclude [0] (edge r66) (a 22) (a 30) 11 d30 c66 (by decide +kernel)
  have t14 : a 22 ∈ [0,10] := remove (a 22) 11 [0,10,11] t13 b14
  have b15 : a 26 ≠ 3 := exclude [0,4] (fun u v => edge r69 v u) (a 26) (a 24) 3 d24 c69 (by decide +kernel)
  have t15 : a 26 ∈ [0,2,5] := remove (a 26) 3 [0,2,3,5] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t14 (And.intro t10 (And.intro t11 (t15)))))))))

theorem chunk19 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,2,5])
    (d24 : a 24 ∈ [0,4])
    (d28 : a 28 ∈ [0])
    (d25 : a 25 ∈ [0,2])
    (d27 : a 27 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 26 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 31 ∈ [0,13,14,15,16,17] := by
  have b0 : a 26 ≠ 5 := exclude [0,4] (fun u v => edge r69 v u) (a 26) (a 24) 5 d24 c69 (by decide +kernel)
  have t0 : a 26 ∈ [0,2] := remove (a 26) 5 [0,2,5] d26 b0
  have b1 : a 24 ≠ 4 := exclude [0] (edge r70) (a 24) (a 28) 4 d28 c70 (by decide +kernel)
  have t1 : a 24 ∈ [0] := remove (a 24) 4 [0,4] d24 b1
  have b2 : a 25 ≠ 2 := exclude [0] (edge r71) (a 25) (a 27) 2 d27 c71 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b2
  have b3 : a 26 ≠ 2 := exclude [0] (edge r73) (a 26) (a 27) 2 d27 c73 (by decide +kernel)
  have t3 : a 26 ∈ [0] := remove (a 26) 2 [0,2] t0 b3
  have b4 : a 31 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 1 d27 c75 (by decide +kernel)
  have t4 : a 31 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d31 b4
  have b5 : a 31 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 2 d27 c75 (by decide +kernel)
  have t5 : a 31 ∈ [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 2 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t4 b5
  have b6 : a 31 ≠ 3 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 3 d27 c75 (by decide +kernel)
  have t6 : a 31 ∈ [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 3 [0,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 31 ≠ 4 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 4 d27 c75 (by decide +kernel)
  have t7 : a 31 ∈ [0,5,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 4 [0,4,5,6,7,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 31 ≠ 5 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 5 d27 c75 (by decide +kernel)
  have t8 : a 31 ∈ [0,6,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 5 [0,5,6,7,8,9,10,11,12,13,14,15,16,17] t7 b8
  have b9 : a 31 ≠ 6 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 6 d27 c75 (by decide +kernel)
  have t9 : a 31 ∈ [0,7,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 6 [0,6,7,8,9,10,11,12,13,14,15,16,17] t8 b9
  have b10 : a 31 ≠ 7 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 7 d27 c75 (by decide +kernel)
  have t10 : a 31 ∈ [0,8,9,10,11,12,13,14,15,16,17] := remove (a 31) 7 [0,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 31 ≠ 8 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 8 d27 c75 (by decide +kernel)
  have t11 : a 31 ∈ [0,9,10,11,12,13,14,15,16,17] := remove (a 31) 8 [0,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 31 ≠ 9 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 9 d27 c75 (by decide +kernel)
  have t12 : a 31 ∈ [0,10,11,12,13,14,15,16,17] := remove (a 31) 9 [0,9,10,11,12,13,14,15,16,17] t11 b12
  have b13 : a 31 ≠ 10 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 10 d27 c75 (by decide +kernel)
  have t13 : a 31 ∈ [0,11,12,13,14,15,16,17] := remove (a 31) 10 [0,10,11,12,13,14,15,16,17] t12 b13
  have b14 : a 31 ≠ 11 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 11 d27 c75 (by decide +kernel)
  have t14 : a 31 ∈ [0,12,13,14,15,16,17] := remove (a 31) 11 [0,11,12,13,14,15,16,17] t13 b14
  have b15 : a 31 ≠ 12 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 12 d27 c75 (by decide +kernel)
  have t15 : a 31 ∈ [0,13,14,15,16,17] := remove (a 31) 12 [0,12,13,14,15,16,17] t14 b15
  exact And.intro t3 (And.intro t1 (And.intro t2 (t15)))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_213
