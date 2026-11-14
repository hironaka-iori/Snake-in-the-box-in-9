import PartitionData205_169
namespace PartitionCover205_169
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,4,5])
    (d17 : a 17 ∈ [0,5])
    (d18 : a 18 ∈ [0,1,2])
    (d20 : a 20 ∈ [0,3,4,5,8,11,16,17])
    (d22 : a 22 ∈ [0,1,4,5])
    (d26 : a 26 ∈ [0,1,4,5])
    (d23 : a 23 ∈ [0,4,8,9,10,11])
    (d19 : a 19 ∈ [0,2])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    : a 30 ∈ [0,1,2,3,6,7,8,9] ∧ a 16 ∈ [0,5] ∧ a 18 ∈ [0,2] ∧ a 20 ∈ [0,4,5,8] ∧ a 22 ∈ [0,4] ∧ a 26 ∈ [0,5] ∧ a 23 ∈ [0,4,9,10,11] := by
  have b0 : a 30 ≠ 4 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,2,3,5,6,7,8,9,10,11] := remove (a 30) 4 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b0
  have b1 : a 30 ≠ 5 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,1,2,3,6,7,8,9,10,11] := remove (a 30) 5 [0,1,2,3,5,6,7,8,9,10,11] t0 b1
  have b2 : a 30 ≠ 10 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,2,3,6,7,8,9,11] := remove (a 30) 10 [0,1,2,3,6,7,8,9,10,11] t1 b2
  have b3 : a 30 ≠ 11 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,2,3,6,7,8,9] := remove (a 30) 11 [0,1,2,3,6,7,8,9,11] t2 b3
  have b4 : a 16 ≠ 1 := exclude [0,5] (edge r48) (a 16) (a 17) 1 d17 c48 (by decide +kernel)
  have t4 : a 16 ∈ [0,4,5] := remove (a 16) 1 [0,1,4,5] d16 b4
  have b5 : a 16 ≠ 4 := exclude [0,5] (edge r48) (a 16) (a 17) 4 d17 c48 (by decide +kernel)
  have t5 : a 16 ∈ [0,5] := remove (a 16) 4 [0,4,5] t4 b5
  have b6 : a 18 ≠ 1 := exclude [0,5] (fun u v => edge r49 v u) (a 18) (a 16) 1 t5 c49 (by decide +kernel)
  have t6 : a 18 ∈ [0,2] := remove (a 18) 1 [0,1,2] d18 b6
  have b7 : a 20 ≠ 3 := exclude [0,5] (fun u v => edge r50 v u) (a 20) (a 16) 3 t5 c50 (by decide +kernel)
  have t7 : a 20 ∈ [0,4,5,8,11,16,17] := remove (a 20) 3 [0,3,4,5,8,11,16,17] d20 b7
  have b8 : a 20 ≠ 11 := exclude [0,5] (fun u v => edge r50 v u) (a 20) (a 16) 11 t5 c50 (by decide +kernel)
  have t8 : a 20 ∈ [0,4,5,8,16,17] := remove (a 20) 11 [0,4,5,8,11,16,17] t7 b8
  have b9 : a 20 ≠ 16 := exclude [0,5] (fun u v => edge r50 v u) (a 20) (a 16) 16 t5 c50 (by decide +kernel)
  have t9 : a 20 ∈ [0,4,5,8,17] := remove (a 20) 16 [0,4,5,8,16,17] t8 b9
  have b10 : a 20 ≠ 17 := exclude [0,5] (fun u v => edge r50 v u) (a 20) (a 16) 17 t5 c50 (by decide +kernel)
  have t10 : a 20 ∈ [0,4,5,8] := remove (a 20) 17 [0,4,5,8,17] t9 b10
  have b11 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r56 v u) (a 22) (a 18) 1 t6 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,4,5] := remove (a 22) 1 [0,1,4,5] d22 b11
  have b12 : a 22 ≠ 5 := exclude [0,2] (fun u v => edge r56 v u) (a 22) (a 18) 5 t6 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,4] := remove (a 22) 5 [0,4,5] t11 b12
  have b13 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 1 t6 c57 (by decide +kernel)
  have t13 : a 26 ∈ [0,4,5] := remove (a 26) 1 [0,1,4,5] d26 b13
  have b14 : a 26 ≠ 4 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 4 t6 c57 (by decide +kernel)
  have t14 : a 26 ∈ [0,5] := remove (a 26) 4 [0,4,5] t13 b14
  have b15 : a 23 ≠ 8 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 8 d19 c58 (by decide +kernel)
  have t15 : a 23 ∈ [0,4,9,10,11] := remove (a 23) 8 [0,4,8,9,10,11] d23 b15
  exact And.intro t3 (And.intro t5 (And.intro t6 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))

theorem chunk9 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,4,9,10,11])
    (d19 : a 19 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2,5])
    (d20 : a 20 ∈ [0,4,5,8])
    (d21 : a 21 ∈ [0,10,11])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d30 : a 30 ∈ [0,1,2,3,6,7,8,9])
    (d22 : a 22 ∈ [0,4])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 23 ∈ [0,4] ∧ a 27 ∈ [0,1] ∧ a 20 ∈ [0,8] ∧ a 21 ∈ [0] ∧ a 29 ∈ [0,1,3,4] ∧ a 30 ∈ [0,2,6,8] ∧ a 31 ∈ [0,1,2,3,5] := by
  have b0 : a 23 ≠ 9 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 9 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,4,10,11] := remove (a 23) 9 [0,4,9,10,11] d23 b0
  have b1 : a 23 ≠ 10 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 10 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,4,11] := remove (a 23) 10 [0,4,10,11] t0 b1
  have b2 : a 23 ≠ 11 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 11 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,4] := remove (a 23) 11 [0,4,11] t1 b2
  have b3 : a 27 ≠ 2 := exclude [0,2] (fun u v => edge r59 v u) (a 27) (a 19) 2 d19 c59 (by decide +kernel)
  have t3 : a 27 ∈ [0,1,5] := remove (a 27) 2 [0,1,2,5] d27 b3
  have b4 : a 27 ≠ 5 := exclude [0,2] (fun u v => edge r59 v u) (a 27) (a 19) 5 d19 c59 (by decide +kernel)
  have t4 : a 27 ∈ [0,1] := remove (a 27) 5 [0,1,5] t3 b4
  have b5 : a 20 ≠ 4 := exclude [0,10,11] (edge r60) (a 20) (a 21) 4 d21 c60 (by decide +kernel)
  have t5 : a 20 ∈ [0,5,8] := remove (a 20) 4 [0,4,5,8] d20 b5
  have b6 : a 20 ≠ 5 := exclude [0,10,11] (edge r60) (a 20) (a 21) 5 d21 c60 (by decide +kernel)
  have t6 : a 20 ∈ [0,8] := remove (a 20) 5 [0,5,8] t5 b6
  have b7 : a 21 ≠ 10 := exclude [0,8] (fun u v => edge r60 v u) (a 21) (a 20) 10 t6 c60 (by decide +kernel)
  have t7 : a 21 ∈ [0,11] := remove (a 21) 10 [0,10,11] d21 b7
  have b8 : a 21 ≠ 11 := exclude [0,8] (fun u v => edge r60 v u) (a 21) (a 20) 11 t6 c60 (by decide +kernel)
  have t8 : a 21 ∈ [0] := remove (a 21) 11 [0,11] t7 b8
  have b9 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 t8 c64 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,3,4,5] := remove (a 29) 2 [0,1,2,3,4,5] d29 b9
  have b10 : a 29 ≠ 5 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 5 t8 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,3,4] := remove (a 29) 5 [0,1,3,4,5] t9 b10
  have b11 : a 30 ≠ 1 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,3,6,7,8,9] := remove (a 30) 1 [0,1,2,3,6,7,8,9] d30 b11
  have b12 : a 30 ≠ 3 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 3 d22 c66 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,6,7,8,9] := remove (a 30) 3 [0,2,3,6,7,8,9] t11 b12
  have b13 : a 30 ≠ 7 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 7 d22 c66 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,6,8,9] := remove (a 30) 7 [0,2,6,7,8,9] t12 b13
  have b14 : a 30 ≠ 9 := exclude [0,4] (fun u v => edge r66 v u) (a 30) (a 22) 9 d22 c66 (by decide +kernel)
  have t14 : a 30 ∈ [0,2,6,8] := remove (a 30) 9 [0,2,6,8,9] t13 b14
  have b15 : a 31 ≠ 4 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 4 t2 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,2,3,5] := remove (a 31) 4 [0,1,2,3,4,5] d31 b15
  exact And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t14 (t15))))))

theorem chunk10 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2,3,5])
    (d23 : a 23 ∈ [0,4])
    (d24 : a 24 ∈ [0,1,2])
    (d25 : a 25 ∈ [0])
    (d29 : a 29 ∈ [0,1,3,4])
    (d30 : a 30 ∈ [0,2,6,8])
    (d26 : a 26 ∈ [0,5])
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 31 ∈ [0,1,2,3] ∧ a 24 ∈ [0] ∧ a 29 ∈ [0,1] ∧ a 30 ∈ [0,2] := by
  have b0 : a 31 ≠ 5 := exclude [0,4] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,1,2,3] := remove (a 31) 5 [0,1,2,3,5] d31 b0
  have b1 : a 24 ≠ 1 := exclude [0] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t1 : a 24 ∈ [0,2] := remove (a 24) 1 [0,1,2] d24 b1
  have b2 : a 24 ≠ 2 := exclude [0] (edge r68) (a 24) (a 25) 2 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 2 [0,2] t1 b2
  have b3 : a 29 ≠ 3 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 3 d25 c72 (by decide +kernel)
  have t3 : a 29 ∈ [0,1,4] := remove (a 29) 3 [0,1,3,4] d29 b3
  have b4 : a 29 ≠ 4 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 4 d25 c72 (by decide +kernel)
  have t4 : a 29 ∈ [0,1] := remove (a 29) 4 [0,1,4] t3 b4
  have b5 : a 30 ≠ 6 := exclude [0,5] (fun u v => edge r74 v u) (a 30) (a 26) 6 d26 c74 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,8] := remove (a 30) 6 [0,2,6,8] d30 b5
  have b6 : a 30 ≠ 8 := exclude [0,5] (fun u v => edge r74 v u) (a 30) (a 26) 8 d26 c74 (by decide +kernel)
  have t6 : a 30 ∈ [0,2] := remove (a 30) 8 [0,2,8] t5 b6
  exact And.intro t0 (And.intro t2 (And.intro t4 (t6)))

theorem chunk11 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,13])
    (d4 : a 4 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d20 : a 20 ∈ [0,8])
    (d7 : a 7 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,4])
    (d15 : a 15 ∈ [0,5])
    (d10 : a 10 ∈ [0,5])
    (d26 : a 26 ∈ [0,5])
    (d11 : a 11 ∈ [0,5])
    (d27 : a 27 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,5])
    (d18 : a 18 ∈ [0,2])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 5 ∈ [0] ∧ a 6 ∈ [0] ∧ a 20 ∈ [0] ∧ a 7 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 10 ∈ [0] ∧ a 26 ∈ [0] ∧ a 11 ∈ [0] ∧ a 27 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0,1] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] := by
  have b0 : a 5 ≠ 13 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 13 d4 c16 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 13 [0,13] d5 b0
  have b1 : a 6 ≠ 2 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b1
  have b2 : a 20 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 8 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0] := remove (a 20) 8 [0,8] d20 b2
  have b3 : a 7 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 2 t0 c20 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b3
  have b4 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 t1 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b4
  have b5 : a 22 ≠ 4 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 4 t1 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0] := remove (a 22) 4 [0,4] d22 b5
  have b6 : a 15 ≠ 5 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 5 t3 c26 (by decide +kernel)
  have t6 : a 15 ∈ [0] := remove (a 15) 5 [0,5] d15 b6
  have b7 : a 10 ≠ 5 := exclude [0] (edge r36) (a 10) (a 14) 5 t4 c36 (by decide +kernel)
  have t7 : a 10 ∈ [0] := remove (a 10) 5 [0,5] d10 b7
  have b8 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 t7 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 5 [0,5] d26 b8
  have b9 : a 11 ≠ 5 := exclude [0] (edge r38) (a 11) (a 15) 5 t6 c38 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 5 [0,5] d11 b9
  have b10 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 t9 c39 (by decide +kernel)
  have t10 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b10
  have b11 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 t4 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b11
  have b12 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 t6 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b12
  have b13 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 t6 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t12 b13
  have b14 : a 16 ≠ 5 := exclude [0] (edge r50) (a 16) (a 20) 5 t2 c50 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 5 [0,5] d16 b14
  have b15 : a 18 ≠ 2 := exclude [0] (edge r56) (a 18) (a 22) 2 t5 c56 (by decide +kernel)
  have t15 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))))))))))))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_169
