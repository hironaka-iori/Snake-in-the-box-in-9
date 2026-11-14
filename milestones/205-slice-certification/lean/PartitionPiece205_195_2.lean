import PartitionData205_195
namespace PartitionCover205_195
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,2,3,4,6,8,9,10,13,15,17])
    (d24 : a 24 ∈ [0,2,3,8])
    (d26 : a 26 ∈ [0,2,9,11])
    (d29 : a 29 ∈ [0,2,4,8])
    (d27 : a 27 ∈ [0,1,2,3])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 25 ∈ [0,9] ∧ a 24 ∈ [0,8] ∧ a 26 ∈ [0,2] ∧ a 29 ∈ [0,4] ∧ a 27 ∈ [0,2,3] := by
  have b0 : a 25 ≠ 4 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t0 : a 25 ∈ [0,2,3,6,8,9,10,13,15,17] := remove (a 25) 4 [0,2,3,4,6,8,9,10,13,15,17] d25 b0
  have b1 : a 25 ≠ 6 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 6 d24 c68 (by decide +kernel)
  have t1 : a 25 ∈ [0,2,3,8,9,10,13,15,17] := remove (a 25) 6 [0,2,3,6,8,9,10,13,15,17] t0 b1
  have b2 : a 25 ≠ 8 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 8 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [0,2,3,9,10,13,15,17] := remove (a 25) 8 [0,2,3,8,9,10,13,15,17] t1 b2
  have b3 : a 25 ≠ 10 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 10 d24 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0,2,3,9,13,15,17] := remove (a 25) 10 [0,2,3,9,10,13,15,17] t2 b3
  have b4 : a 25 ≠ 13 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 13 d24 c68 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,3,9,15,17] := remove (a 25) 13 [0,2,3,9,13,15,17] t3 b4
  have b5 : a 25 ≠ 15 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 15 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,3,9,17] := remove (a 25) 15 [0,2,3,9,15,17] t4 b5
  have b6 : a 25 ≠ 17 := exclude [0,2,3,8] (fun u v => edge r68 v u) (a 25) (a 24) 17 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,2,3,9] := remove (a 25) 17 [0,2,3,9,17] t5 b6
  have b7 : a 24 ≠ 2 := exclude [0,2,9,11] (edge r69) (a 24) (a 26) 2 d26 c69 (by decide +kernel)
  have t7 : a 24 ∈ [0,3,8] := remove (a 24) 2 [0,2,3,8] d24 b7
  have b8 : a 24 ≠ 3 := exclude [0,2,9,11] (edge r69) (a 24) (a 26) 3 d26 c69 (by decide +kernel)
  have t8 : a 24 ∈ [0,8] := remove (a 24) 3 [0,3,8] t7 b8
  have b9 : a 26 ≠ 9 := exclude [0,8] (fun u v => edge r69 v u) (a 26) (a 24) 9 t8 c69 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,11] := remove (a 26) 9 [0,2,9,11] d26 b9
  have b10 : a 26 ≠ 11 := exclude [0,8] (fun u v => edge r69 v u) (a 26) (a 24) 11 t8 c69 (by decide +kernel)
  have t10 : a 26 ∈ [0,2] := remove (a 26) 11 [0,2,11] t9 b10
  have b11 : a 25 ≠ 2 := exclude [0,2,4,8] (edge r72) (a 25) (a 29) 2 d29 c72 (by decide +kernel)
  have t11 : a 25 ∈ [0,3,9] := remove (a 25) 2 [0,2,3,9] t6 b11
  have b12 : a 25 ≠ 3 := exclude [0,2,4,8] (edge r72) (a 25) (a 29) 3 d29 c72 (by decide +kernel)
  have t12 : a 25 ∈ [0,9] := remove (a 25) 3 [0,3,9] t11 b12
  have b13 : a 29 ≠ 2 := exclude [0,9] (fun u v => edge r72 v u) (a 29) (a 25) 2 t12 c72 (by decide +kernel)
  have t13 : a 29 ∈ [0,4,8] := remove (a 29) 2 [0,2,4,8] d29 b13
  have b14 : a 29 ≠ 8 := exclude [0,9] (fun u v => edge r72 v u) (a 29) (a 25) 8 t12 c72 (by decide +kernel)
  have t14 : a 29 ∈ [0,4] := remove (a 29) 8 [0,4,8] t13 b14
  have b15 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 1 t10 c73 (by decide +kernel)
  have t15 : a 27 ∈ [0,2,3] := remove (a 27) 1 [0,1,2,3] d27 b15
  exact And.intro t12 (And.intro t8 (And.intro t10 (And.intro t14 (t15))))

theorem chunk9 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,2,3])
    (d26 : a 26 ∈ [0,2])
    (d31 : a 31 ∈ [0,2,3,9])
    (d30 : a 30 ∈ [0,1,4,5])
    (d28 : a 28 ∈ [0,7])
    (d16 : a 16 ∈ [0,1,12,13])
    (d24 : a 24 ∈ [0,8])
    (d18 : a 18 ∈ [0,4,5,7,8,11])
    (d19 : a 19 ∈ [0,3])
    (c51 : edge r51 (a 16) (a 24)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 27 ∈ [0,2] ∧ a 31 ∈ [0,9] ∧ a 30 ∈ [0,4] ∧ a 16 ∈ [0,12] ∧ a 18 ∈ [0,5] := by
  have b0 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 3 d26 c73 (by decide +kernel)
  have t0 : a 27 ∈ [0,2] := remove (a 27) 3 [0,2,3] d27 b0
  have b1 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 2 t0 c75 (by decide +kernel)
  have t1 : a 31 ∈ [0,3,9] := remove (a 31) 2 [0,2,3,9] d31 b1
  have b2 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r75 v u) (a 31) (a 27) 3 t0 c75 (by decide +kernel)
  have t2 : a 31 ∈ [0,9] := remove (a 31) 3 [0,3,9] t1 b2
  have b3 : a 30 ≠ 1 := exclude [0,7] (fun u v => edge r77 v u) (a 30) (a 28) 1 d28 c77 (by decide +kernel)
  have t3 : a 30 ∈ [0,4,5] := remove (a 30) 1 [0,1,4,5] d30 b3
  have b4 : a 30 ≠ 5 := exclude [0,7] (fun u v => edge r77 v u) (a 30) (a 28) 5 d28 c77 (by decide +kernel)
  have t4 : a 30 ∈ [0,4] := remove (a 30) 5 [0,4,5] t3 b4
  have b5 : a 16 ≠ 1 := exclude [0,8] (edge r51) (a 16) (a 24) 1 d24 c51 (by decide +kernel)
  have t5 : a 16 ∈ [0,12,13] := remove (a 16) 1 [0,1,12,13] d16 b5
  have b6 : a 16 ≠ 13 := exclude [0,8] (edge r51) (a 16) (a 24) 13 d24 c51 (by decide +kernel)
  have t6 : a 16 ∈ [0,12] := remove (a 16) 13 [0,12,13] t5 b6
  have b7 : a 18 ≠ 4 := exclude [0,3] (edge r55) (a 18) (a 19) 4 d19 c55 (by decide +kernel)
  have t7 : a 18 ∈ [0,5,7,8,11] := remove (a 18) 4 [0,4,5,7,8,11] d18 b7
  have b8 : a 18 ≠ 7 := exclude [0,3] (edge r55) (a 18) (a 19) 7 d19 c55 (by decide +kernel)
  have t8 : a 18 ∈ [0,5,8,11] := remove (a 18) 7 [0,5,7,8,11] t7 b8
  have b9 : a 18 ≠ 8 := exclude [0,3] (edge r55) (a 18) (a 19) 8 d19 c55 (by decide +kernel)
  have t9 : a 18 ∈ [0,5,11] := remove (a 18) 8 [0,5,8,11] t8 b9
  have b10 : a 18 ≠ 11 := exclude [0,3] (edge r55) (a 18) (a 19) 11 d19 c55 (by decide +kernel)
  have t10 : a 18 ∈ [0,5] := remove (a 18) 11 [0,5,11] t9 b10
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (t10))))

theorem chunk10 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d17 : a 17 ∈ [0,3])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,1])
    (d10 : a 10 ∈ [0,3])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d22 : a 22 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d24 : a 24 ∈ [0,8])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 7 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 8 ∈ [0] ∧ a 24 ∈ [0] := by
  have b0 : a 3 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 2 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b2
  have b3 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0] := remove (a 17) 3 [0,3] d17 b3
  have b4 : a 2 ≠ 2 := exclude [0] (edge r9) (a 2) (a 3) 2 t0 c9 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b4
  have b5 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 t4 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b5
  have b6 : a 10 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 3 t4 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0] := remove (a 10) 3 [0,3] d10 b6
  have b7 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t5 c17 (by decide +kernel)
  have t7 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b7
  have b8 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t7 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b8
  have b9 : a 7 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 2 t1 c20 (by decide +kernel)
  have t9 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b9
  have b10 : a 13 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 1 t1 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b10
  have b11 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 t1 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b11
  have b12 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 t5 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b12
  have b13 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 t5 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b13
  have b14 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 t2 c28 (by decide +kernel)
  have t14 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b14
  have b15 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 t14 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0] := remove (a 24) 8 [0,8] d24 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk11 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,6])
    (d10 : a 10 ∈ [0])
    (d26 : a 26 ∈ [0,2])
    (d28 : a 28 ∈ [0,7])
    (d12 : a 12 ∈ [0])
    (d15 : a 15 ∈ [0,2])
    (d13 : a 13 ∈ [0])
    (d29 : a 29 ∈ [0,4])
    (d30 : a 30 ∈ [0,4])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,9])
    (d16 : a 16 ∈ [0,12])
    (d17 : a 17 ∈ [0])
    (d18 : a 18 ∈ [0,5])
    (d22 : a 22 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d23 : a 23 ∈ [0,2])
    (d25 : a 25 ∈ [0,9])
    (d24 : a 24 ∈ [0])
    (d27 : a 27 ∈ [0,2])
    (d19 : a 19 ∈ [0,3])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 11 ∈ [0] ∧ a 26 ∈ [0] ∧ a 28 ∈ [0] ∧ a 15 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 20 ∈ [0] ∧ a 23 ∈ [0] ∧ a 25 ∈ [0] ∧ a 27 ∈ [0] ∧ a 19 ∈ [0] := by
  have b0 : a 11 ≠ 6 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 6 d10 c35 (by decide +kernel)
  have t0 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b0
  have b1 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b1
  have b2 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0] := remove (a 28) 7 [0,7] d28 b2
  have b3 : a 15 ≠ 2 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 2 d13 c43 (by decide +kernel)
  have t3 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b3
  have b4 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0] := remove (a 29) 4 [0,4] d29 b4
  have b5 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0] := remove (a 30) 4 [0,4] d30 b5
  have b6 : a 31 ≠ 9 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 9 t3 c47 (by decide +kernel)
  have t6 : a 31 ∈ [0] := remove (a 31) 9 [0,9] d31 b6
  have b7 : a 16 ≠ 12 := exclude [0] (edge r48) (a 16) (a 17) 12 d17 c48 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 12 [0,12] d16 b7
  have b8 : a 18 ≠ 5 := exclude [0] (edge r56) (a 18) (a 22) 5 d22 c56 (by decide +kernel)
  have t8 : a 18 ∈ [0] := remove (a 18) 5 [0,5] d18 b8
  have b9 : a 20 ≠ 1 := exclude [0] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t9 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b9
  have b10 : a 23 ≠ 2 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 2 d21 c63 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b10
  have b11 : a 25 ≠ 9 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 9 d24 c68 (by decide +kernel)
  have t11 : a 25 ∈ [0] := remove (a 25) 9 [0,9] d25 b11
  have b12 : a 27 ≠ 2 := exclude [0] (fun u v => edge r73 v u) (a 27) (a 26) 2 t1 c73 (by decide +kernel)
  have t12 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b12
  have b13 : a 19 ≠ 3 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 3 t8 c55 (by decide +kernel)
  have t13 : a 19 ∈ [0] := remove (a 19) 3 [0,3] d19 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_195
