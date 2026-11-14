import PartitionData205_214
namespace PartitionCover205_214
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,2,5])
    (d10 : a 10 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3,4,5,6,7,8])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,2])
    (d12 : a 12 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 14 ∈ [0] ∧ a 26 ∈ [0,1,3,4] ∧ a 27 ∈ [0,2] ∧ a 28 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := by
  have b0 : a 14 ≠ 5 := exclude [0,2] (fun u v => edge r36 v u) (a 14) (a 10) 5 d10 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,2] := remove (a 14) 5 [0,2,5] d14 b0
  have b1 : a 26 ≠ 2 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0,1,3,4,5,6,7,8] := remove (a 26) 2 [0,1,2,3,4,5,6,7,8] d26 b1
  have b2 : a 26 ≠ 5 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,3,4,6,7,8] := remove (a 26) 5 [0,1,3,4,5,6,7,8] t1 b2
  have b3 : a 26 ≠ 6 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 6 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,3,4,7,8] := remove (a 26) 6 [0,1,3,4,6,7,8] t2 b3
  have b4 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 7 d10 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,3,4,8] := remove (a 26) 7 [0,1,3,4,7,8] t3 b4
  have b5 : a 26 ≠ 8 := exclude [0,2] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,3,4] := remove (a 26) 8 [0,1,3,4,8] t4 b5
  have b6 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b6
  have b7 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t7 : a 27 ∈ [0,2,4,5] := remove (a 27) 3 [0,2,3,4,5] t6 b7
  have b8 : a 27 ≠ 4 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0,2,5] := remove (a 27) 4 [0,2,4,5] t7 b8
  have b9 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,2] := remove (a 27) 5 [0,2,5] t8 b9
  have b10 : a 14 ≠ 2 := exclude [0] (fun u v => edge r41 v u) (a 14) (a 12) 2 d12 c41 (by decide +kernel)
  have t10 : a 14 ∈ [0] := remove (a 14) 2 [0,2] t0 b10
  have b11 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b11
  have b12 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 7 [0,2,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t10 (And.intro t5 (And.intro t9 (t15)))

theorem chunk9 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 28 ∈ [0,2,6,8] ∧ a 29 ∈ [0,1,3,4,5] := by
  have b0 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,6,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 9 [0,2,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d28 b0
  have b1 : a 28 ≠ 10 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 10 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,6,8,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 10 [0,2,6,8,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 28 ≠ 11 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 11 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,6,8,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 11 [0,2,6,8,11,12,13,14,15,16,17,18,19,20,21,22,23] t1 b2
  have b3 : a 28 ≠ 12 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 12 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,6,8,13,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 12 [0,2,6,8,12,13,14,15,16,17,18,19,20,21,22,23] t2 b3
  have b4 : a 28 ≠ 13 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 13 d12 c42 (by decide +kernel)
  have t4 : a 28 ∈ [0,2,6,8,14,15,16,17,18,19,20,21,22,23] := remove (a 28) 13 [0,2,6,8,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 28 ≠ 14 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 14 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,6,8,15,16,17,18,19,20,21,22,23] := remove (a 28) 14 [0,2,6,8,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 28 ≠ 15 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 15 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,6,8,16,17,18,19,20,21,22,23] := remove (a 28) 15 [0,2,6,8,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 28 ≠ 16 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 16 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,6,8,17,18,19,20,21,22,23] := remove (a 28) 16 [0,2,6,8,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 28 ≠ 17 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 17 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,2,6,8,18,19,20,21,22,23] := remove (a 28) 17 [0,2,6,8,17,18,19,20,21,22,23] t7 b8
  have b9 : a 28 ≠ 18 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 18 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,2,6,8,19,20,21,22,23] := remove (a 28) 18 [0,2,6,8,18,19,20,21,22,23] t8 b9
  have b10 : a 28 ≠ 19 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 19 d12 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,6,8,20,21,22,23] := remove (a 28) 19 [0,2,6,8,19,20,21,22,23] t9 b10
  have b11 : a 28 ≠ 20 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 20 d12 c42 (by decide +kernel)
  have t11 : a 28 ∈ [0,2,6,8,21,22,23] := remove (a 28) 20 [0,2,6,8,20,21,22,23] t10 b11
  have b12 : a 28 ≠ 21 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 21 d12 c42 (by decide +kernel)
  have t12 : a 28 ∈ [0,2,6,8,22,23] := remove (a 28) 21 [0,2,6,8,21,22,23] t11 b12
  have b13 : a 28 ≠ 22 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 22 d12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,2,6,8,23] := remove (a 28) 22 [0,2,6,8,22,23] t12 b13
  have b14 : a 28 ≠ 23 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 23 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,6,8] := remove (a 28) 23 [0,2,6,8,23] t13 b14
  have b15 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,1,3,4,5] := remove (a 29) 2 [0,1,2,3,4,5] d29 b15
  exact And.intro t14 (t15)

theorem chunk10 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,3,4,5])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0])
    (d16 : a 16 ∈ [0,1,6,7])
    (d17 : a 17 ∈ [0,1,2,3,4,5])
    (d20 : a 20 ∈ [0])
    (d21 : a 21 ∈ [0,1])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 29 ∈ [0,1] ∧ a 30 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,4,5] := remove (a 29) 3 [0,1,3,4,5] d29 b0
  have b1 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,5] := remove (a 29) 4 [0,1,4,5] t0 b1
  have b2 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,1] := remove (a 29) 5 [0,1,5] t1 b2
  have b3 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,3,4,5] := remove (a 30) 1 [0,1,2,3,4,5] d30 b3
  have b4 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,3,4,5] := remove (a 30) 2 [0,2,3,4,5] t3 b4
  have b5 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,4,5] := remove (a 30) 3 [0,3,4,5] t4 b5
  have b6 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,5] := remove (a 30) 4 [0,4,5] t5 b6
  have b7 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0] := remove (a 30) 5 [0,5] t6 b7
  have b8 : a 16 ≠ 1 := exclude [0,1,2,3,4,5] (edge r48) (a 16) (a 17) 1 d17 c48 (by decide +kernel)
  have t8 : a 16 ∈ [0,6,7] := remove (a 16) 1 [0,1,6,7] d16 b8
  have b9 : a 16 ≠ 7 := exclude [0,1,2,3,4,5] (edge r48) (a 16) (a 17) 7 d17 c48 (by decide +kernel)
  have t9 : a 16 ∈ [0,6] := remove (a 16) 7 [0,6,7] t8 b9
  have b10 : a 17 ≠ 1 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 1 t9 c48 (by decide +kernel)
  have t10 : a 17 ∈ [0,2,3,4,5] := remove (a 17) 1 [0,1,2,3,4,5] d17 b10
  have b11 : a 17 ≠ 3 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 3 t9 c48 (by decide +kernel)
  have t11 : a 17 ∈ [0,2,4,5] := remove (a 17) 3 [0,2,3,4,5] t10 b11
  have b12 : a 17 ≠ 4 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 4 t9 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,2,5] := remove (a 17) 4 [0,2,4,5] t11 b12
  have b13 : a 17 ≠ 5 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 5 t9 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0,2] := remove (a 17) 5 [0,2,5] t12 b13
  have b14 : a 16 ≠ 6 := exclude [0] (edge r50) (a 16) (a 20) 6 d20 c50 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 6 [0,6] t9 b14
  have b15 : a 17 ≠ 2 := exclude [0,1] (edge r53) (a 17) (a 21) 2 d21 c53 (by decide +kernel)
  have t15 : a 17 ∈ [0] := remove (a 17) 2 [0,2] t13 b15
  exact And.intro t2 (And.intro t7 (And.intro t14 (t15)))

theorem chunk11 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d28 : a 28 ∈ [0,2,6,8])
    (d20 : a 20 ∈ [0])
    (d26 : a 26 ∈ [0,1,3,4])
    (d24 : a 24 ∈ [0,6])
    (d25 : a 25 ∈ [0,4])
    (d29 : a 29 ∈ [0,1])
    (d30 : a 30 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (d27 : a 27 ∈ [0,2])
    (d3 : a 3 ∈ [0,2])
    (d7 : a 7 ∈ [0])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 21 ∈ [0] ∧ a 28 ∈ [0] ∧ a 26 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 29 ∈ [0] ∧ a 31 ∈ [0] ∧ a 3 ∈ [0] := by
  have b0 : a 21 ≠ 1 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t0 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b0
  have b1 : a 28 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 2 d20 c62 (by decide +kernel)
  have t1 : a 28 ∈ [0,6,8] := remove (a 28) 2 [0,2,6,8] d28 b1
  have b2 : a 28 ≠ 6 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 6 d20 c62 (by decide +kernel)
  have t2 : a 28 ∈ [0,8] := remove (a 28) 6 [0,6,8] t1 b2
  have b3 : a 26 ≠ 1 := exclude [0,6] (fun u v => edge r69 v u) (a 26) (a 24) 1 d24 c69 (by decide +kernel)
  have t3 : a 26 ∈ [0,3,4] := remove (a 26) 1 [0,1,3,4] d26 b3
  have b4 : a 26 ≠ 4 := exclude [0,6] (fun u v => edge r69 v u) (a 26) (a 24) 4 d24 c69 (by decide +kernel)
  have t4 : a 26 ∈ [0,3] := remove (a 26) 4 [0,3,4] t3 b4
  have b5 : a 24 ≠ 6 := exclude [0,8] (edge r70) (a 24) (a 28) 6 t2 c70 (by decide +kernel)
  have t5 : a 24 ∈ [0] := remove (a 24) 6 [0,6] d24 b5
  have b6 : a 28 ≠ 8 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 8 t5 c70 (by decide +kernel)
  have t6 : a 28 ∈ [0] := remove (a 28) 8 [0,8] t2 b6
  have b7 : a 25 ≠ 4 := exclude [0,1] (edge r72) (a 25) (a 29) 4 d29 c72 (by decide +kernel)
  have t7 : a 25 ∈ [0] := remove (a 25) 4 [0,4] d25 b7
  have b8 : a 29 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 1 t7 c72 (by decide +kernel)
  have t8 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b8
  have b9 : a 26 ≠ 3 := exclude [0] (edge r74) (a 26) (a 30) 3 d30 c74 (by decide +kernel)
  have t9 : a 26 ∈ [0] := remove (a 26) 3 [0,3] t4 b9
  have b10 : a 31 ≠ 1 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 1 d27 c75 (by decide +kernel)
  have t10 : a 31 ∈ [0,2,3,4,5] := remove (a 31) 1 [0,1,2,3,4,5] d31 b10
  have b11 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 3 d27 c75 (by decide +kernel)
  have t11 : a 31 ∈ [0,2,4,5] := remove (a 31) 3 [0,2,3,4,5] t10 b11
  have b12 : a 31 ≠ 4 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 4 d27 c75 (by decide +kernel)
  have t12 : a 31 ∈ [0,2,5] := remove (a 31) 4 [0,2,4,5] t11 b12
  have b13 : a 31 ≠ 5 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 5 d27 c75 (by decide +kernel)
  have t13 : a 31 ∈ [0,2] := remove (a 31) 5 [0,2,5] t12 b13
  have b14 : a 31 ≠ 2 := exclude [0] (fun u v => edge r78 v u) (a 31) (a 29) 2 t8 c78 (by decide +kernel)
  have t14 : a 31 ∈ [0] := remove (a 31) 2 [0,2] t13 b14
  have b15 : a 3 ≠ 2 := exclude [0] (edge r13) (a 3) (a 7) 2 d7 c13 (by decide +kernel)
  have t15 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b15
  exact And.intro t0 (And.intro t6 (And.intro t9 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t14 (t15)))))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_214
