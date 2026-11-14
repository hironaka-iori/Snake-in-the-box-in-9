import PartitionData205_162
namespace PartitionCover205_162
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d19 : a 19 ∈ [0])
    (d27 : a 27 ∈ [0,2])
    (d20 : a 20 ∈ [0,1,4,5])
    (d21 : a 21 ∈ [0,1])
    (d22 : a 22 ∈ [0,2,7,8])
    (d28 : a 28 ∈ [0,1,2,3,4,5])
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    : a 23 ∈ [0,2] ∧ a 27 ∈ [0] ∧ a 20 ∈ [0,1] ∧ a 22 ∈ [0,2] ∧ a 28 ∈ [0,1,3,4,5] := by
  have b0 : a 23 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d23 b0
  have b1 : a 23 ≠ 3 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 23) 3 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 23 ≠ 4 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t2 : a 23 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 23) 4 [0,2,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 23 ≠ 5 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t3 : a 23 ∈ [0,2,6,7,8,9,10,11] := remove (a 23) 5 [0,2,5,6,7,8,9,10,11] t2 b3
  have b4 : a 23 ≠ 6 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 6 d19 c58 (by decide +kernel)
  have t4 : a 23 ∈ [0,2,7,8,9,10,11] := remove (a 23) 6 [0,2,6,7,8,9,10,11] t3 b4
  have b5 : a 23 ≠ 7 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,2,8,9,10,11] := remove (a 23) 7 [0,2,7,8,9,10,11] t4 b5
  have b6 : a 23 ≠ 8 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 8 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,2,9,10,11] := remove (a 23) 8 [0,2,8,9,10,11] t5 b6
  have b7 : a 23 ≠ 9 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 9 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,2,10,11] := remove (a 23) 9 [0,2,9,10,11] t6 b7
  have b8 : a 23 ≠ 10 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 10 d19 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,2,11] := remove (a 23) 10 [0,2,10,11] t7 b8
  have b9 : a 23 ≠ 11 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 11 d19 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,2] := remove (a 23) 11 [0,2,11] t8 b9
  have b10 : a 27 ≠ 2 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 2 d19 c59 (by decide +kernel)
  have t10 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b10
  have b11 : a 20 ≠ 4 := exclude [0,1] (edge r60) (a 20) (a 21) 4 d21 c60 (by decide +kernel)
  have t11 : a 20 ∈ [0,1,5] := remove (a 20) 4 [0,1,4,5] d20 b11
  have b12 : a 20 ≠ 5 := exclude [0,1] (edge r60) (a 20) (a 21) 5 d21 c60 (by decide +kernel)
  have t12 : a 20 ∈ [0,1] := remove (a 20) 5 [0,1,5] t11 b12
  have b13 : a 22 ≠ 7 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 7 t12 c61 (by decide +kernel)
  have t13 : a 22 ∈ [0,2,8] := remove (a 22) 7 [0,2,7,8] d22 b13
  have b14 : a 22 ≠ 8 := exclude [0,1] (fun u v => edge r61 v u) (a 22) (a 20) 8 t12 c61 (by decide +kernel)
  have t14 : a 22 ∈ [0,2] := remove (a 22) 8 [0,2,8] t13 b14
  have b15 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 2 t12 c62 (by decide +kernel)
  have t15 : a 28 ∈ [0,1,3,4,5] := remove (a 28) 2 [0,1,2,3,4,5] d28 b15
  exact And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,3,4,5])
    (d20 : a 20 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2])
    (d21 : a 21 ∈ [0,1])
    (d30 : a 30 ∈ [0,1,3,4,6,7])
    (d22 : a 22 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6,7,8])
    (d23 : a 23 ∈ [0,2])
    (d24 : a 24 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (c62 : edge r62 (a 20) (a 28)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    : a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0,1,6,7] ∧ a 31 ∈ [0,1,2] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 3 d20 c62 (by decide +kernel)
  have t0 : a 28 ∈ [0,1,4,5] := remove (a 28) 3 [0,1,3,4,5] d28 b0
  have b1 : a 28 ≠ 4 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 4 d20 c62 (by decide +kernel)
  have t1 : a 28 ∈ [0,1,5] := remove (a 28) 4 [0,1,4,5] t0 b1
  have b2 : a 28 ≠ 5 := exclude [0,1] (fun u v => edge r62 v u) (a 28) (a 20) 5 d20 c62 (by decide +kernel)
  have t2 : a 28 ∈ [0,1] := remove (a 28) 5 [0,1,5] t1 b2
  have b3 : a 29 ≠ 1 := exclude [0,1] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t3 : a 29 ∈ [0,2] := remove (a 29) 1 [0,1,2] d29 b3
  have b4 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r64 v u) (a 29) (a 21) 2 d21 c64 (by decide +kernel)
  have t4 : a 29 ∈ [0] := remove (a 29) 2 [0,2] t3 b4
  have b5 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 3 d22 c66 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,4,6,7] := remove (a 30) 3 [0,1,3,4,6,7] d30 b5
  have b6 : a 30 ≠ 4 := exclude [0,2] (fun u v => edge r66 v u) (a 30) (a 22) 4 d22 c66 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,6,7] := remove (a 30) 4 [0,1,4,6,7] t5 b6
  have b7 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 3 d23 c67 (by decide +kernel)
  have t7 : a 31 ∈ [0,1,2,4,5,6,7,8] := remove (a 31) 3 [0,1,2,3,4,5,6,7,8] d31 b7
  have b8 : a 31 ≠ 4 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 4 d23 c67 (by decide +kernel)
  have t8 : a 31 ∈ [0,1,2,5,6,7,8] := remove (a 31) 4 [0,1,2,4,5,6,7,8] t7 b8
  have b9 : a 31 ≠ 5 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 5 d23 c67 (by decide +kernel)
  have t9 : a 31 ∈ [0,1,2,6,7,8] := remove (a 31) 5 [0,1,2,5,6,7,8] t8 b9
  have b10 : a 31 ≠ 6 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 6 d23 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,2,7,8] := remove (a 31) 6 [0,1,2,6,7,8] t9 b10
  have b11 : a 31 ≠ 7 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 7 d23 c67 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,2,8] := remove (a 31) 7 [0,1,2,7,8] t10 b11
  have b12 : a 31 ≠ 8 := exclude [0,2] (fun u v => edge r67 v u) (a 31) (a 23) 8 d23 c67 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,2] := remove (a 31) 8 [0,1,2,8] t11 b12
  have b13 : a 24 ≠ 1 := exclude [0] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t13 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b13
  have b14 : a 26 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 1 t13 c69 (by decide +kernel)
  have t14 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b14
  have b15 : a 28 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 1 t13 c70 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 1 [0,1] t2 b15
  exact And.intro t15 (And.intro t4 (And.intro t6 (And.intro t12 (And.intro t13 (t14)))))

theorem chunk6 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,6,7])
    (d26 : a 26 ∈ [0])
    (d31 : a 31 ∈ [0,1,2])
    (d27 : a 27 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d4 : a 4 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17])
    (d20 : a 20 ∈ [0,1])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 5 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17] ∧ a 6 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17] ∧ a 4 ∈ [0,1,5,8,9,10,11,14,15,16,17] := by
  have b0 : a 30 ≠ 6 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 6 d26 c74 (by decide +kernel)
  have t0 : a 30 ∈ [0,1,7] := remove (a 30) 6 [0,1,6,7] d30 b0
  have b1 : a 30 ≠ 7 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 7 d26 c74 (by decide +kernel)
  have t1 : a 30 ∈ [0,1] := remove (a 30) 7 [0,1,7] t0 b1
  have b2 : a 31 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 1 d27 c75 (by decide +kernel)
  have t2 : a 31 ∈ [0,2] := remove (a 31) 1 [0,1,2] d31 b2
  have b3 : a 31 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 2 d27 c75 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 2 [0,2] t2 b3
  have b4 : a 30 ≠ 1 := exclude [0] (edge r79) (a 30) (a 31) 1 t3 c79 (by decide +kernel)
  have t4 : a 30 ∈ [0] := remove (a 30) 1 [0,1] t1 b4
  have b5 : a 5 ≠ 6 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r16 v u) (a 5) (a 4) 6 d4 c16 (by decide +kernel)
  have t5 : a 5 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d5 b5
  have b6 : a 5 ≠ 7 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r16 v u) (a 5) (a 4) 7 d4 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 5) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t5 b6
  have b7 : a 5 ≠ 12 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r16 v u) (a 5) (a 4) 12 d4 c16 (by decide +kernel)
  have t7 : a 5 ∈ [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] := remove (a 5) 12 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] t6 b7
  have b8 : a 5 ≠ 13 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r16 v u) (a 5) (a 4) 13 d4 c16 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17] := remove (a 5) 13 [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] t7 b8
  have b9 : a 6 ≠ 6 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r17 v u) (a 6) (a 4) 6 d4 c17 (by decide +kernel)
  have t9 : a 6 ∈ [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] := remove (a 6) 6 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] d6 b9
  have b10 : a 6 ≠ 7 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r17 v u) (a 6) (a 4) 7 d4 c17 (by decide +kernel)
  have t10 : a 6 ∈ [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] := remove (a 6) 7 [0,1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17] t9 b10
  have b11 : a 6 ≠ 12 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r17 v u) (a 6) (a 4) 12 d4 c17 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] := remove (a 6) 12 [0,1,2,3,4,5,8,9,10,11,12,13,14,15,16,17] t10 b11
  have b12 : a 6 ≠ 13 := exclude [0,1,2,3,4,5,8,9,10,11,14,15,16,17] (fun u v => edge r17 v u) (a 6) (a 4) 13 d4 c17 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17] := remove (a 6) 13 [0,1,2,3,4,5,8,9,10,11,13,14,15,16,17] t11 b12
  have b13 : a 4 ≠ 2 := exclude [0,1] (edge r19) (a 4) (a 20) 2 d20 c19 (by decide +kernel)
  have t13 : a 4 ∈ [0,1,3,4,5,8,9,10,11,14,15,16,17] := remove (a 4) 2 [0,1,2,3,4,5,8,9,10,11,14,15,16,17] d4 b13
  have b14 : a 4 ≠ 3 := exclude [0,1] (edge r19) (a 4) (a 20) 3 d20 c19 (by decide +kernel)
  have t14 : a 4 ∈ [0,1,4,5,8,9,10,11,14,15,16,17] := remove (a 4) 3 [0,1,3,4,5,8,9,10,11,14,15,16,17] t13 b14
  have b15 : a 4 ≠ 4 := exclude [0,1] (edge r19) (a 4) (a 20) 4 d20 c19 (by decide +kernel)
  have t15 : a 4 ∈ [0,1,5,8,9,10,11,14,15,16,17] := remove (a 4) 4 [0,1,4,5,8,9,10,11,14,15,16,17] t14 b15
  exact And.intro t4 (And.intro t3 (And.intro t8 (And.intro t12 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,5,8,9,10,11,14,15,16,17])
    (d20 : a 20 ∈ [0,1])
    (d5 : a 5 ∈ [0,1,2,3,4,5,8,9,10,11,14,15,16,17])
    (d21 : a 21 ∈ [0,1])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 4 ∈ [0,1,14,16] ∧ a 5 ∈ [0,1,15,16,17] := by
  have b0 : a 4 ≠ 5 := exclude [0,1] (edge r19) (a 4) (a 20) 5 d20 c19 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,8,9,10,11,14,15,16,17] := remove (a 4) 5 [0,1,5,8,9,10,11,14,15,16,17] d4 b0
  have b1 : a 4 ≠ 8 := exclude [0,1] (edge r19) (a 4) (a 20) 8 d20 c19 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,9,10,11,14,15,16,17] := remove (a 4) 8 [0,1,8,9,10,11,14,15,16,17] t0 b1
  have b2 : a 4 ≠ 9 := exclude [0,1] (edge r19) (a 4) (a 20) 9 d20 c19 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,10,11,14,15,16,17] := remove (a 4) 9 [0,1,9,10,11,14,15,16,17] t1 b2
  have b3 : a 4 ≠ 10 := exclude [0,1] (edge r19) (a 4) (a 20) 10 d20 c19 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,11,14,15,16,17] := remove (a 4) 10 [0,1,10,11,14,15,16,17] t2 b3
  have b4 : a 4 ≠ 11 := exclude [0,1] (edge r19) (a 4) (a 20) 11 d20 c19 (by decide +kernel)
  have t4 : a 4 ∈ [0,1,14,15,16,17] := remove (a 4) 11 [0,1,11,14,15,16,17] t3 b4
  have b5 : a 4 ≠ 15 := exclude [0,1] (edge r19) (a 4) (a 20) 15 d20 c19 (by decide +kernel)
  have t5 : a 4 ∈ [0,1,14,16,17] := remove (a 4) 15 [0,1,14,15,16,17] t4 b5
  have b6 : a 4 ≠ 17 := exclude [0,1] (edge r19) (a 4) (a 20) 17 d20 c19 (by decide +kernel)
  have t6 : a 4 ∈ [0,1,14,16] := remove (a 4) 17 [0,1,14,16,17] t5 b6
  have b7 : a 5 ≠ 2 := exclude [0,1] (edge r22) (a 5) (a 21) 2 d21 c22 (by decide +kernel)
  have t7 : a 5 ∈ [0,1,3,4,5,8,9,10,11,14,15,16,17] := remove (a 5) 2 [0,1,2,3,4,5,8,9,10,11,14,15,16,17] d5 b7
  have b8 : a 5 ≠ 3 := exclude [0,1] (edge r22) (a 5) (a 21) 3 d21 c22 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,4,5,8,9,10,11,14,15,16,17] := remove (a 5) 3 [0,1,3,4,5,8,9,10,11,14,15,16,17] t7 b8
  have b9 : a 5 ≠ 4 := exclude [0,1] (edge r22) (a 5) (a 21) 4 d21 c22 (by decide +kernel)
  have t9 : a 5 ∈ [0,1,5,8,9,10,11,14,15,16,17] := remove (a 5) 4 [0,1,4,5,8,9,10,11,14,15,16,17] t8 b9
  have b10 : a 5 ≠ 5 := exclude [0,1] (edge r22) (a 5) (a 21) 5 d21 c22 (by decide +kernel)
  have t10 : a 5 ∈ [0,1,8,9,10,11,14,15,16,17] := remove (a 5) 5 [0,1,5,8,9,10,11,14,15,16,17] t9 b10
  have b11 : a 5 ≠ 8 := exclude [0,1] (edge r22) (a 5) (a 21) 8 d21 c22 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,9,10,11,14,15,16,17] := remove (a 5) 8 [0,1,8,9,10,11,14,15,16,17] t10 b11
  have b12 : a 5 ≠ 9 := exclude [0,1] (edge r22) (a 5) (a 21) 9 d21 c22 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,10,11,14,15,16,17] := remove (a 5) 9 [0,1,9,10,11,14,15,16,17] t11 b12
  have b13 : a 5 ≠ 10 := exclude [0,1] (edge r22) (a 5) (a 21) 10 d21 c22 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,11,14,15,16,17] := remove (a 5) 10 [0,1,10,11,14,15,16,17] t12 b13
  have b14 : a 5 ≠ 11 := exclude [0,1] (edge r22) (a 5) (a 21) 11 d21 c22 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,14,15,16,17] := remove (a 5) 11 [0,1,11,14,15,16,17] t13 b14
  have b15 : a 5 ≠ 14 := exclude [0,1] (edge r22) (a 5) (a 21) 14 d21 c22 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,15,16,17] := remove (a 5) 14 [0,1,14,15,16,17] t14 b15
  exact And.intro t6 (t15)

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_162
