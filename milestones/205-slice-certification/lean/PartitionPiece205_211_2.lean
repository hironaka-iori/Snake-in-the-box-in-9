import PartitionData205_211
namespace PartitionCover205_211
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,5,6,7,8,9])
    (d13 : a 13 ∈ [0,3])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,3])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 29 ∈ [0,2,6,7] ∧ a 30 ∈ [0,2,4,6,17,18,19,20,21,22,23] := by
  have b0 : a 29 ≠ 5 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,6,7,8,9] := remove (a 29) 5 [0,2,5,6,7,8,9] d29 b0
  have b1 : a 29 ≠ 8 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,2,6,7,9] := remove (a 29) 8 [0,2,6,7,8,9] t0 b1
  have b2 : a 29 ≠ 9 := exclude [0,3] (fun u v => edge r44 v u) (a 29) (a 13) 9 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,2,6,7] := remove (a 29) 9 [0,2,6,7,9] t1 b2
  have b3 : a 30 ≠ 1 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] d30 b3
  have b4 : a 30 ≠ 3 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t3 b4
  have b5 : a 30 ≠ 5 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 5 [0,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t4 b5
  have b6 : a 30 ≠ 7 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 7 [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t5 b6
  have b7 : a 30 ≠ 8 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,4,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 8 [0,2,4,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t6 b7
  have b8 : a 30 ≠ 9 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,2,4,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 9 [0,2,4,6,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t7 b8
  have b9 : a 30 ≠ 10 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,4,6,11,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 10 [0,2,4,6,10,11,12,13,14,15,16,17,18,19,20,21,22,23] t8 b9
  have b10 : a 30 ≠ 11 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,4,6,12,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 11 [0,2,4,6,11,12,13,14,15,16,17,18,19,20,21,22,23] t9 b10
  have b11 : a 30 ≠ 12 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 12 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,4,6,13,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 12 [0,2,4,6,12,13,14,15,16,17,18,19,20,21,22,23] t10 b11
  have b12 : a 30 ≠ 13 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 13 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,4,6,14,15,16,17,18,19,20,21,22,23] := remove (a 30) 13 [0,2,4,6,13,14,15,16,17,18,19,20,21,22,23] t11 b12
  have b13 : a 30 ≠ 14 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 14 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,4,6,15,16,17,18,19,20,21,22,23] := remove (a 30) 14 [0,2,4,6,14,15,16,17,18,19,20,21,22,23] t12 b13
  have b14 : a 30 ≠ 15 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 15 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,2,4,6,16,17,18,19,20,21,22,23] := remove (a 30) 15 [0,2,4,6,15,16,17,18,19,20,21,22,23] t13 b14
  have b15 : a 30 ≠ 16 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 16 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,4,6,17,18,19,20,21,22,23] := remove (a 30) 16 [0,2,4,6,16,17,18,19,20,21,22,23] t14 b15
  exact And.intro t2 (t15)

theorem chunk9 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,4,6,17,18,19,20,21,22,23])
    (d14 : a 14 ∈ [0,3])
    (d18 : a 18 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,2])
    (d19 : a 19 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,2])
    (d21 : a 21 ∈ [0,1,2,4])
    (d26 : a 26 ∈ [0,1,3,4,6,7,9])
    (d27 : a 27 ∈ [0,1,6,7])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 30 ∈ [0,2,4,6,18,20] ∧ a 18 ∈ [0,2] ∧ a 19 ∈ [0,2] ∧ a 21 ∈ [0,1] ∧ a 26 ∈ [0,4,6] ∧ a 27 ∈ [0,6] := by
  have b0 : a 30 ≠ 17 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 17 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,4,6,18,19,20,21,22,23] := remove (a 30) 17 [0,2,4,6,17,18,19,20,21,22,23] d30 b0
  have b1 : a 30 ≠ 19 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 19 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,4,6,18,20,21,22,23] := remove (a 30) 19 [0,2,4,6,18,19,20,21,22,23] t0 b1
  have b2 : a 30 ≠ 21 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 21 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,2,4,6,18,20,22,23] := remove (a 30) 21 [0,2,4,6,18,20,21,22,23] t1 b2
  have b3 : a 30 ≠ 22 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 22 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,4,6,18,20,23] := remove (a 30) 22 [0,2,4,6,18,20,22,23] t2 b3
  have b4 : a 30 ≠ 23 := exclude [0,3] (fun u v => edge r46 v u) (a 30) (a 14) 23 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,4,6,18,20] := remove (a 30) 23 [0,2,4,6,18,20,23] t3 b4
  have b5 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 1 d16 c49 (by decide +kernel)
  have t5 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b5
  have b6 : a 18 ≠ 3 := exclude [0,2] (fun u v => edge r49 v u) (a 18) (a 16) 3 d16 c49 (by decide +kernel)
  have t6 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] t5 b6
  have b7 : a 19 ≠ 1 := exclude [0,2] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t7 : a 19 ∈ [0,2] := remove (a 19) 1 [0,1,2] d19 b7
  have b8 : a 21 ≠ 2 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,4] := remove (a 21) 2 [0,1,2,4] d21 b8
  have b9 : a 21 ≠ 4 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t9 : a 21 ∈ [0,1] := remove (a 21) 4 [0,1,4] t8 b9
  have b10 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 1 t6 c57 (by decide +kernel)
  have t10 : a 26 ∈ [0,3,4,6,7,9] := remove (a 26) 1 [0,1,3,4,6,7,9] d26 b10
  have b11 : a 26 ≠ 3 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 3 t6 c57 (by decide +kernel)
  have t11 : a 26 ∈ [0,4,6,7,9] := remove (a 26) 3 [0,3,4,6,7,9] t10 b11
  have b12 : a 26 ≠ 7 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 7 t6 c57 (by decide +kernel)
  have t12 : a 26 ∈ [0,4,6,9] := remove (a 26) 7 [0,4,6,7,9] t11 b12
  have b13 : a 26 ≠ 9 := exclude [0,2] (fun u v => edge r57 v u) (a 26) (a 18) 9 t6 c57 (by decide +kernel)
  have t13 : a 26 ∈ [0,4,6] := remove (a 26) 9 [0,4,6,9] t12 b13
  have b14 : a 27 ≠ 1 := exclude [0,2] (fun u v => edge r59 v u) (a 27) (a 19) 1 t7 c59 (by decide +kernel)
  have t14 : a 27 ∈ [0,6,7] := remove (a 27) 1 [0,1,6,7] d27 b14
  have b15 : a 27 ≠ 7 := exclude [0,2] (fun u v => edge r59 v u) (a 27) (a 19) 7 t7 c59 (by decide +kernel)
  have t15 : a 27 ∈ [0,6] := remove (a 27) 7 [0,6,7] t14 b15
  exact And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk10 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,1,6,7])
    (d20 : a 20 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,4])
    (d21 : a 21 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (d24 : a 24 ∈ [0,2])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,4,6])
    (d29 : a 29 ∈ [0,2,6,7])
    (d28 : a 28 ∈ [0,9])
    (d30 : a 30 ∈ [0,2,4,6,18,20])
    (c61 : edge r61 (a 20) (a 22)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 22 ∈ [0,6] ∧ a 23 ∈ [0,1] ∧ a 31 ∈ [0,3] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0,6] ∧ a 29 ∈ [0,6] ∧ a 30 ∈ [0,18] := by
  have b0 : a 22 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 1 d20 c61 (by decide +kernel)
  have t0 : a 22 ∈ [0,6,7] := remove (a 22) 1 [0,1,6,7] d22 b0
  have b1 : a 22 ≠ 7 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 7 d20 c61 (by decide +kernel)
  have t1 : a 22 ∈ [0,6] := remove (a 22) 7 [0,6,7] t0 b1
  have b2 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 2 d21 c63 (by decide +kernel)
  have t2 : a 23 ∈ [0,1,4] := remove (a 23) 2 [0,1,2,4] d23 b2
  have b3 : a 23 ≠ 4 := exclude [0,1] (fun u v => edge r63 v u) (a 23) (a 21) 4 d21 c63 (by decide +kernel)
  have t3 : a 23 ∈ [0,1] := remove (a 23) 4 [0,1,4] t2 b3
  have b4 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 1 t3 c67 (by decide +kernel)
  have t4 : a 31 ∈ [0,2,3,4,5] := remove (a 31) 1 [0,1,2,3,4,5] d31 b4
  have b5 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 2 t3 c67 (by decide +kernel)
  have t5 : a 31 ∈ [0,3,4,5] := remove (a 31) 2 [0,2,3,4,5] t4 b5
  have b6 : a 31 ≠ 4 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 4 t3 c67 (by decide +kernel)
  have t6 : a 31 ∈ [0,3,5] := remove (a 31) 4 [0,3,4,5] t5 b6
  have b7 : a 31 ≠ 5 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 5 t3 c67 (by decide +kernel)
  have t7 : a 31 ∈ [0,3] := remove (a 31) 5 [0,3,5] t6 b7
  have b8 : a 24 ≠ 2 := exclude [0,3] (edge r68) (a 24) (a 25) 2 d25 c68 (by decide +kernel)
  have t8 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b8
  have b9 : a 26 ≠ 4 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 4 t8 c69 (by decide +kernel)
  have t9 : a 26 ∈ [0,6] := remove (a 26) 4 [0,4,6] d26 b9
  have b10 : a 29 ≠ 2 := exclude [0,9] (fun u v => edge r76 v u) (a 29) (a 28) 2 d28 c76 (by decide +kernel)
  have t10 : a 29 ∈ [0,6,7] := remove (a 29) 2 [0,2,6,7] d29 b10
  have b11 : a 29 ≠ 7 := exclude [0,9] (fun u v => edge r76 v u) (a 29) (a 28) 7 d28 c76 (by decide +kernel)
  have t11 : a 29 ∈ [0,6] := remove (a 29) 7 [0,6,7] t10 b11
  have b12 : a 30 ≠ 2 := exclude [0,9] (fun u v => edge r77 v u) (a 30) (a 28) 2 d28 c77 (by decide +kernel)
  have t12 : a 30 ∈ [0,4,6,18,20] := remove (a 30) 2 [0,2,4,6,18,20] d30 b12
  have b13 : a 30 ≠ 4 := exclude [0,9] (fun u v => edge r77 v u) (a 30) (a 28) 4 d28 c77 (by decide +kernel)
  have t13 : a 30 ∈ [0,6,18,20] := remove (a 30) 4 [0,4,6,18,20] t12 b13
  have b14 : a 30 ≠ 6 := exclude [0,9] (fun u v => edge r77 v u) (a 30) (a 28) 6 d28 c77 (by decide +kernel)
  have t14 : a 30 ∈ [0,18,20] := remove (a 30) 6 [0,6,18,20] t13 b14
  have b15 : a 30 ≠ 20 := exclude [0,9] (fun u v => edge r77 v u) (a 30) (a 28) 20 d28 c77 (by decide +kernel)
  have t15 : a 30 ∈ [0,18] := remove (a 30) 20 [0,18,20] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t11 (t15))))))

theorem chunk11 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1,2])
    (d11 : a 11 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,6,7])
    (d14 : a 14 ∈ [0,3])
    (d7 : a 7 ∈ [0,1,2,4])
    (d15 : a 15 ∈ [0,1])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0,6] ∧ a 7 ∈ [0,1] := by
  have b0 : a 3 ≠ 1 := exclude [0,1] (edge r14) (a 3) (a 11) 1 d11 c14 (by decide +kernel)
  have t0 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b0
  have b1 : a 3 ≠ 2 := exclude [0,1] (edge r14) (a 3) (a 11) 2 d11 c14 (by decide +kernel)
  have t1 : a 3 ∈ [0] := remove (a 3) 2 [0,2] t0 b1
  have b2 : a 6 ≠ 1 := exclude [0,3] (edge r24) (a 6) (a 14) 1 d14 c24 (by decide +kernel)
  have t2 : a 6 ∈ [0,6,7] := remove (a 6) 1 [0,1,6,7] d6 b2
  have b3 : a 6 ≠ 7 := exclude [0,3] (edge r24) (a 6) (a 14) 7 d14 c24 (by decide +kernel)
  have t3 : a 6 ∈ [0,6] := remove (a 6) 7 [0,6,7] t2 b3
  have b4 : a 7 ≠ 2 := exclude [0,1] (edge r26) (a 7) (a 15) 2 d15 c26 (by decide +kernel)
  have t4 : a 7 ∈ [0,1,4] := remove (a 7) 2 [0,1,2,4] d7 b4
  have b5 : a 7 ≠ 4 := exclude [0,1] (edge r26) (a 7) (a 15) 4 d15 c26 (by decide +kernel)
  have t5 : a 7 ∈ [0,1] := remove (a 7) 4 [0,1,4] t4 b5
  exact And.intro t1 (And.intro t3 (t5))

#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_211
