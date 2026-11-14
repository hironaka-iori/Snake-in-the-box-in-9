import PartitionData205_191
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,12,17,18,19])
    (d21 : a 21 ∈ [0,4])
    (d25 : a 25 ∈ [0,1,3,4,6,7,8,17,18,19,21,23])
    (d24 : a 24 ∈ [0,16])
    (d26 : a 26 ∈ [0,1,2,12])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (c63 : edge r63 (a 21) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 23 ∈ [0,12] ∧ a 25 ∈ [0,1,18,21] ∧ a 26 ∈ [0,12] ∧ a 27 ∈ [0,3,5] := by
  have b0 : a 23 ≠ 17 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 17 d21 c63 (by decide +kernel)
  have t0 : a 23 ∈ [0,12,18,19] := remove (a 23) 17 [0,12,17,18,19] d23 b0
  have b1 : a 23 ≠ 18 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 18 d21 c63 (by decide +kernel)
  have t1 : a 23 ∈ [0,12,19] := remove (a 23) 18 [0,12,18,19] t0 b1
  have b2 : a 23 ≠ 19 := exclude [0,4] (fun u v => edge r63 v u) (a 23) (a 21) 19 d21 c63 (by decide +kernel)
  have t2 : a 23 ∈ [0,12] := remove (a 23) 19 [0,12,19] t1 b2
  have b3 : a 25 ≠ 3 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 3 d24 c68 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,4,6,7,8,17,18,19,21,23] := remove (a 25) 3 [0,1,3,4,6,7,8,17,18,19,21,23] d25 b3
  have b4 : a 25 ≠ 4 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,6,7,8,17,18,19,21,23] := remove (a 25) 4 [0,1,4,6,7,8,17,18,19,21,23] t3 b4
  have b5 : a 25 ≠ 6 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 6 d24 c68 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,7,8,17,18,19,21,23] := remove (a 25) 6 [0,1,6,7,8,17,18,19,21,23] t4 b5
  have b6 : a 25 ≠ 7 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 7 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,8,17,18,19,21,23] := remove (a 25) 7 [0,1,7,8,17,18,19,21,23] t5 b6
  have b7 : a 25 ≠ 8 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 8 d24 c68 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,17,18,19,21,23] := remove (a 25) 8 [0,1,8,17,18,19,21,23] t6 b7
  have b8 : a 25 ≠ 17 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 17 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [0,1,18,19,21,23] := remove (a 25) 17 [0,1,17,18,19,21,23] t7 b8
  have b9 : a 25 ≠ 19 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 19 d24 c68 (by decide +kernel)
  have t9 : a 25 ∈ [0,1,18,21,23] := remove (a 25) 19 [0,1,18,19,21,23] t8 b9
  have b10 : a 25 ≠ 23 := exclude [0,16] (fun u v => edge r68 v u) (a 25) (a 24) 23 d24 c68 (by decide +kernel)
  have t10 : a 25 ∈ [0,1,18,21] := remove (a 25) 23 [0,1,18,21,23] t9 b10
  have b11 : a 26 ≠ 1 := exclude [0,1,2,3,4,5] (edge r73) (a 26) (a 27) 1 d27 c73 (by decide +kernel)
  have t11 : a 26 ∈ [0,2,12] := remove (a 26) 1 [0,1,2,12] d26 b11
  have b12 : a 26 ≠ 2 := exclude [0,1,2,3,4,5] (edge r73) (a 26) (a 27) 2 d27 c73 (by decide +kernel)
  have t12 : a 26 ∈ [0,12] := remove (a 26) 2 [0,2,12] t11 b12
  have b13 : a 27 ≠ 1 := exclude [0,12] (fun u v => edge r73 v u) (a 27) (a 26) 1 t12 c73 (by decide +kernel)
  have t13 : a 27 ∈ [0,2,3,4,5] := remove (a 27) 1 [0,1,2,3,4,5] d27 b13
  have b14 : a 27 ≠ 2 := exclude [0,12] (fun u v => edge r73 v u) (a 27) (a 26) 2 t12 c73 (by decide +kernel)
  have t14 : a 27 ∈ [0,3,4,5] := remove (a 27) 2 [0,2,3,4,5] t13 b14
  have b15 : a 27 ≠ 4 := exclude [0,12] (fun u v => edge r73 v u) (a 27) (a 26) 4 t12 c73 (by decide +kernel)
  have t15 : a 27 ∈ [0,3,5] := remove (a 27) 4 [0,3,4,5] t14 b15
  exact And.intro t2 (And.intro t10 (And.intro t12 (t15)))

theorem chunk21 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,3,5])
    (d26 : a 26 ∈ [0,12])
    (d30 : a 30 ∈ [0,1,4,5])
    (d29 : a 29 ∈ [0,1,18,21])
    (d31 : a 31 ∈ [0,3,18,19])
    (d2 : a 2 ∈ [0,1,2,3,8,9,10,11])
    (d6 : a 6 ∈ [0,9])
    (d3 : a 3 ∈ [0,1,2,3,8,9,10,11])
    (d11 : a 11 ∈ [0,4])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 27 ∈ [0,3] ∧ a 30 ∈ [0,5] ∧ a 29 ∈ [0,18] ∧ a 31 ∈ [0,18] ∧ a 2 ∈ [0,9] ∧ a 3 ∈ [0,8,9,10,11] := by
  have b0 : a 27 ≠ 5 := exclude [0,12] (fun u v => edge r73 v u) (a 27) (a 26) 5 d26 c73 (by decide +kernel)
  have t0 : a 27 ∈ [0,3] := remove (a 27) 5 [0,3,5] d27 b0
  have b1 : a 30 ≠ 1 := exclude [0,12] (fun u v => edge r74 v u) (a 30) (a 26) 1 d26 c74 (by decide +kernel)
  have t1 : a 30 ∈ [0,4,5] := remove (a 30) 1 [0,1,4,5] d30 b1
  have b2 : a 30 ≠ 4 := exclude [0,12] (fun u v => edge r74 v u) (a 30) (a 26) 4 d26 c74 (by decide +kernel)
  have t2 : a 30 ∈ [0,5] := remove (a 30) 4 [0,4,5] t1 b2
  have b3 : a 29 ≠ 1 := exclude [0,3,18,19] (edge r78) (a 29) (a 31) 1 d31 c78 (by decide +kernel)
  have t3 : a 29 ∈ [0,18,21] := remove (a 29) 1 [0,1,18,21] d29 b3
  have b4 : a 29 ≠ 21 := exclude [0,3,18,19] (edge r78) (a 29) (a 31) 21 d31 c78 (by decide +kernel)
  have t4 : a 29 ∈ [0,18] := remove (a 29) 21 [0,18,21] t3 b4
  have b5 : a 31 ≠ 3 := exclude [0,18] (fun u v => edge r78 v u) (a 31) (a 29) 3 t4 c78 (by decide +kernel)
  have t5 : a 31 ∈ [0,18,19] := remove (a 31) 3 [0,3,18,19] d31 b5
  have b6 : a 31 ≠ 19 := exclude [0,18] (fun u v => edge r78 v u) (a 31) (a 29) 19 t4 c78 (by decide +kernel)
  have t6 : a 31 ∈ [0,18] := remove (a 31) 19 [0,18,19] t5 b6
  have b7 : a 2 ≠ 1 := exclude [0,9] (edge r10) (a 2) (a 6) 1 d6 c10 (by decide +kernel)
  have t7 : a 2 ∈ [0,2,3,8,9,10,11] := remove (a 2) 1 [0,1,2,3,8,9,10,11] d2 b7
  have b8 : a 2 ≠ 2 := exclude [0,9] (edge r10) (a 2) (a 6) 2 d6 c10 (by decide +kernel)
  have t8 : a 2 ∈ [0,3,8,9,10,11] := remove (a 2) 2 [0,2,3,8,9,10,11] t7 b8
  have b9 : a 2 ≠ 3 := exclude [0,9] (edge r10) (a 2) (a 6) 3 d6 c10 (by decide +kernel)
  have t9 : a 2 ∈ [0,8,9,10,11] := remove (a 2) 3 [0,3,8,9,10,11] t8 b9
  have b10 : a 2 ≠ 8 := exclude [0,9] (edge r10) (a 2) (a 6) 8 d6 c10 (by decide +kernel)
  have t10 : a 2 ∈ [0,9,10,11] := remove (a 2) 8 [0,8,9,10,11] t9 b10
  have b11 : a 2 ≠ 10 := exclude [0,9] (edge r10) (a 2) (a 6) 10 d6 c10 (by decide +kernel)
  have t11 : a 2 ∈ [0,9,11] := remove (a 2) 10 [0,9,10,11] t10 b11
  have b12 : a 2 ≠ 11 := exclude [0,9] (edge r10) (a 2) (a 6) 11 d6 c10 (by decide +kernel)
  have t12 : a 2 ∈ [0,9] := remove (a 2) 11 [0,9,11] t11 b12
  have b13 : a 3 ≠ 1 := exclude [0,4] (edge r14) (a 3) (a 11) 1 d11 c14 (by decide +kernel)
  have t13 : a 3 ∈ [0,2,3,8,9,10,11] := remove (a 3) 1 [0,1,2,3,8,9,10,11] d3 b13
  have b14 : a 3 ≠ 2 := exclude [0,4] (edge r14) (a 3) (a 11) 2 d11 c14 (by decide +kernel)
  have t14 : a 3 ∈ [0,3,8,9,10,11] := remove (a 3) 2 [0,2,3,8,9,10,11] t13 b14
  have b15 : a 3 ≠ 3 := exclude [0,4] (edge r14) (a 3) (a 11) 3 d11 c14 (by decide +kernel)
  have t15 : a 3 ∈ [0,8,9,10,11] := remove (a 3) 3 [0,3,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t12 (t15)))))

theorem chunk22 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,8,9,10,11])
    (d11 : a 11 ∈ [0,4])
    (d19 : a 19 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,1,3])
    (d15 : a 15 ∈ [0,21])
    (d8 : a 8 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,5])
    (d16 : a 16 ∈ [0,5,6,7])
    (d17 : a 17 ∈ [0,1,3,14])
    (d18 : a 18 ∈ [0,13,15,19])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    : a 3 ∈ [0,9] ∧ a 19 ∈ [0,1,2,6,7,8] ∧ a 7 ∈ [0] ∧ a 8 ∈ [0,3] ∧ a 16 ∈ [0,5] ∧ a 17 ∈ [0,3] ∧ a 18 ∈ [0,13] := by
  have b0 : a 3 ≠ 8 := exclude [0,4] (edge r14) (a 3) (a 11) 8 d11 c14 (by decide +kernel)
  have t0 : a 3 ∈ [0,9,10,11] := remove (a 3) 8 [0,8,9,10,11] d3 b0
  have b1 : a 3 ≠ 10 := exclude [0,4] (edge r14) (a 3) (a 11) 10 d11 c14 (by decide +kernel)
  have t1 : a 3 ∈ [0,9,11] := remove (a 3) 10 [0,9,10,11] t0 b1
  have b2 : a 3 ≠ 11 := exclude [0,4] (edge r14) (a 3) (a 11) 11 d11 c14 (by decide +kernel)
  have t2 : a 3 ∈ [0,9] := remove (a 3) 11 [0,9,11] t1 b2
  have b3 : a 19 ≠ 3 := exclude [0,9] (fun u v => edge r15 v u) (a 19) (a 3) 3 t2 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,2,4,5,6,7,8] := remove (a 19) 3 [0,1,2,3,4,5,6,7,8] d19 b3
  have b4 : a 19 ≠ 4 := exclude [0,9] (fun u v => edge r15 v u) (a 19) (a 3) 4 t2 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,1,2,5,6,7,8] := remove (a 19) 4 [0,1,2,4,5,6,7,8] t3 b4
  have b5 : a 19 ≠ 5 := exclude [0,9] (fun u v => edge r15 v u) (a 19) (a 3) 5 t2 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0,1,2,6,7,8] := remove (a 19) 5 [0,1,2,5,6,7,8] t4 b5
  have b6 : a 7 ≠ 1 := exclude [0,21] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t6 : a 7 ∈ [0,3] := remove (a 7) 1 [0,1,3] d7 b6
  have b7 : a 7 ≠ 3 := exclude [0,21] (edge r26) (a 7) (a 15) 3 d15 c26 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 3 [0,3] t6 b7
  have b8 : a 8 ≠ 1 := exclude [0,5] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t8 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b8
  have b9 : a 8 ≠ 2 := exclude [0,5] (edge r28) (a 8) (a 9) 2 d9 c28 (by decide +kernel)
  have t9 : a 8 ∈ [0,3] := remove (a 8) 2 [0,2,3] t8 b9
  have b10 : a 16 ≠ 6 := exclude [0,1,3,14] (edge r48) (a 16) (a 17) 6 d17 c48 (by decide +kernel)
  have t10 : a 16 ∈ [0,5,7] := remove (a 16) 6 [0,5,6,7] d16 b10
  have b11 : a 16 ≠ 7 := exclude [0,1,3,14] (edge r48) (a 16) (a 17) 7 d17 c48 (by decide +kernel)
  have t11 : a 16 ∈ [0,5] := remove (a 16) 7 [0,5,7] t10 b11
  have b12 : a 17 ≠ 1 := exclude [0,5] (fun u v => edge r48 v u) (a 17) (a 16) 1 t11 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,3,14] := remove (a 17) 1 [0,1,3,14] d17 b12
  have b13 : a 17 ≠ 14 := exclude [0,5] (fun u v => edge r48 v u) (a 17) (a 16) 14 t11 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0,3] := remove (a 17) 14 [0,3,14] t12 b13
  have b14 : a 18 ≠ 15 := exclude [0,1,2,6,7,8] (edge r55) (a 18) (a 19) 15 t5 c55 (by decide +kernel)
  have t14 : a 18 ∈ [0,13,19] := remove (a 18) 15 [0,13,15,19] d18 b14
  have b15 : a 18 ≠ 19 := exclude [0,1,2,6,7,8] (edge r55) (a 18) (a 19) 19 t5 c55 (by decide +kernel)
  have t15 : a 18 ∈ [0,13] := remove (a 18) 19 [0,13,19] t14 b15
  exact And.intro t2 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t13 (t15))))))

theorem chunk23 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1,2,6,7,8])
    (d18 : a 18 ∈ [0,13])
    (d25 : a 25 ∈ [0,1,18,21])
    (d29 : a 29 ∈ [0,18])
    (c55 : edge r55 (a 18) (a 19)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 19 ∈ [0,6] ∧ a 25 ∈ [0,18] := by
  have b0 : a 19 ≠ 1 := exclude [0,13] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t0 : a 19 ∈ [0,2,6,7,8] := remove (a 19) 1 [0,1,2,6,7,8] d19 b0
  have b1 : a 19 ≠ 2 := exclude [0,13] (fun u v => edge r55 v u) (a 19) (a 18) 2 d18 c55 (by decide +kernel)
  have t1 : a 19 ∈ [0,6,7,8] := remove (a 19) 2 [0,2,6,7,8] t0 b1
  have b2 : a 19 ≠ 7 := exclude [0,13] (fun u v => edge r55 v u) (a 19) (a 18) 7 d18 c55 (by decide +kernel)
  have t2 : a 19 ∈ [0,6,8] := remove (a 19) 7 [0,6,7,8] t1 b2
  have b3 : a 19 ≠ 8 := exclude [0,13] (fun u v => edge r55 v u) (a 19) (a 18) 8 d18 c55 (by decide +kernel)
  have t3 : a 19 ∈ [0,6] := remove (a 19) 8 [0,6,8] t2 b3
  have b4 : a 25 ≠ 1 := exclude [0,18] (edge r72) (a 25) (a 29) 1 d29 c72 (by decide +kernel)
  have t4 : a 25 ∈ [0,18,21] := remove (a 25) 1 [0,1,18,21] d25 b4
  have b5 : a 25 ≠ 21 := exclude [0,18] (edge r72) (a 25) (a 29) 21 d29 c72 (by decide +kernel)
  have t5 : a 25 ∈ [0,18] := remove (a 25) 21 [0,18,21] t4 b5
  exact And.intro t3 (t5)

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_191
