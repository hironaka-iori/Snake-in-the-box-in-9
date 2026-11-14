import PartitionData205_191
namespace PartitionCover205_191
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,9])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,4])
    (d2 : a 2 ∈ [0,9])
    (d6 : a 6 ∈ [0,9])
    (d10 : a 10 ∈ [0,5])
    (d11 : a 11 ∈ [0,4])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,20])
    (d20 : a 20 ∈ [0,3])
    (d13 : a 13 ∈ [0,6])
    (d21 : a 21 ∈ [0,4])
    (d14 : a 14 ∈ [0,9])
    (d22 : a 22 ∈ [0,3])
    (d8 : a 8 ∈ [0,3])
    (d24 : a 24 ∈ [0,16])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 8 ∈ [0] ∧ a 24 ∈ [0] := by
  have b0 : a 3 ≠ 9 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 9 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 9 [0,9] d3 b0
  have b1 : a 5 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 4 [0,4] d5 b1
  have b2 : a 2 ≠ 9 := exclude [0] (edge r9) (a 2) (a 3) 9 t0 c9 (by decide +kernel)
  have t2 : a 2 ∈ [0] := remove (a 2) 9 [0,9] d2 b2
  have b3 : a 6 ≠ 9 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 9 t2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 9 [0,9] d6 b3
  have b4 : a 10 ≠ 5 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 5 t2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [0] := remove (a 10) 5 [0,5] d10 b4
  have b5 : a 11 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 4 t0 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 4 [0,4] d11 b5
  have b6 : a 19 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 6 t0 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 6 [0,6] d19 b6
  have b7 : a 4 ≠ 1 := exclude [0] (edge r16) (a 4) (a 5) 1 t1 c16 (by decide +kernel)
  have t7 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b7
  have b8 : a 12 ≠ 20 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 20 t7 c18 (by decide +kernel)
  have t8 : a 12 ∈ [0] := remove (a 12) 20 [0,20] d12 b8
  have b9 : a 20 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 3 t7 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0] := remove (a 20) 3 [0,3] d20 b9
  have b10 : a 13 ≠ 6 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 6 t1 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 6 [0,6] d13 b10
  have b11 : a 21 ≠ 4 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 4 t1 c22 (by decide +kernel)
  have t11 : a 21 ∈ [0] := remove (a 21) 4 [0,4] d21 b11
  have b12 : a 14 ≠ 9 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 9 t3 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0] := remove (a 14) 9 [0,9] d14 b12
  have b13 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 t3 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0] := remove (a 22) 3 [0,3] d22 b13
  have b14 : a 8 ≠ 3 := exclude [0] (edge r29) (a 8) (a 10) 3 t4 c29 (by decide +kernel)
  have t14 : a 8 ∈ [0] := remove (a 8) 3 [0,3] d8 b14
  have b15 : a 24 ≠ 16 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 16 t14 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0] := remove (a 24) 16 [0,16] d24 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk25 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,12])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,21])
    (d11 : a 11 ∈ [0])
    (d29 : a 29 ∈ [0,18])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,5])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,18])
    (d16 : a 16 ∈ [0,5])
    (d20 : a 20 ∈ [0])
    (d18 : a 18 ∈ [0,13])
    (d19 : a 19 ∈ [0])
    (d23 : a 23 ∈ [0,12])
    (d25 : a 25 ∈ [0,18])
    (d24 : a 24 ∈ [0])
    (d27 : a 27 ∈ [0,3])
    (d9 : a 9 ∈ [0,5])
    (d8 : a 8 ∈ [0])
    (d17 : a 17 ∈ [0,3])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 23 ∈ [0] ∧ a 25 ∈ [0] ∧ a 27 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 26 ≠ 12 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 12 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0] := remove (a 26) 12 [0,12] d26 b0
  have b1 : a 15 ≠ 21 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 21 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [0] := remove (a 15) 21 [0,21] d15 b1
  have b2 : a 29 ≠ 18 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 18 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0] := remove (a 29) 18 [0,18] d29 b2
  have b3 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 5 [0,5] d30 b3
  have b4 : a 31 ≠ 18 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 18 t1 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0] := remove (a 31) 18 [0,18] d31 b4
  have b5 : a 16 ≠ 5 := exclude [0] (edge r50) (a 16) (a 20) 5 d20 c50 (by decide +kernel)
  have t5 : a 16 ∈ [0] := remove (a 16) 5 [0,5] d16 b5
  have b6 : a 18 ≠ 13 := exclude [0] (edge r55) (a 18) (a 19) 13 d19 c55 (by decide +kernel)
  have t6 : a 18 ∈ [0] := remove (a 18) 13 [0,13] d18 b6
  have b7 : a 23 ≠ 12 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 12 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0] := remove (a 23) 12 [0,12] d23 b7
  have b8 : a 25 ≠ 18 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 18 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [0] := remove (a 25) 18 [0,18] d25 b8
  have b9 : a 27 ≠ 3 := exclude [0] (fun u v => edge r73 v u) (a 27) (a 26) 3 t0 c73 (by decide +kernel)
  have t9 : a 27 ∈ [0] := remove (a 27) 3 [0,3] d27 b9
  have b10 : a 9 ≠ 5 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 5 d8 c28 (by decide +kernel)
  have t10 : a 9 ∈ [0] := remove (a 9) 5 [0,5] d9 b10
  have b11 : a 17 ≠ 3 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 3 t5 c48 (by decide +kernel)
  have t11 : a 17 ∈ [0] := remove (a 17) 3 [0,3] d17 b11
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t11)))))))))))

theorem chunk26 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,9])
    (d1 : a 1 ∈ [2])
    (d5 : a 5 ∈ [0,4])
    (d2 : a 2 ∈ [0,9])
    (d6 : a 6 ∈ [0,9])
    (d10 : a 10 ∈ [0,5])
    (d11 : a 11 ∈ [0,4])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,20])
    (d20 : a 20 ∈ [0,3])
    (d13 : a 13 ∈ [0,6])
    (d21 : a 21 ∈ [0,4])
    (d14 : a 14 ∈ [0,9])
    (d22 : a 22 ∈ [0,3])
    (d8 : a 8 ∈ [0,3])
    (d24 : a 24 ∈ [0,16])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 3 ∈ [9] ∧ a 5 ∈ [4] ∧ a 2 ∈ [9] ∧ a 6 ∈ [9] ∧ a 10 ∈ [5] ∧ a 11 ∈ [4] ∧ a 19 ∈ [6] ∧ a 4 ∈ [1] ∧ a 12 ∈ [20] ∧ a 20 ∈ [3] ∧ a 13 ∈ [6] ∧ a 21 ∈ [4] ∧ a 14 ∈ [9] ∧ a 22 ∈ [3] ∧ a 8 ∈ [3] ∧ a 24 ∈ [16] := by
  have b0 : a 3 ≠ 0 := exclude [2] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [9] := remove (a 3) 0 [0,9] d3 b0
  have b1 : a 5 ≠ 0 := exclude [2] (fun u v => edge r6 v u) (a 5) (a 1) 0 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [4] := remove (a 5) 0 [0,4] d5 b1
  have b2 : a 2 ≠ 0 := exclude [9] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t2 : a 2 ∈ [9] := remove (a 2) 0 [0,9] d2 b2
  have b3 : a 6 ≠ 0 := exclude [9] (fun u v => edge r10 v u) (a 6) (a 2) 0 t2 c10 (by decide +kernel)
  have t3 : a 6 ∈ [9] := remove (a 6) 0 [0,9] d6 b3
  have b4 : a 10 ≠ 0 := exclude [9] (fun u v => edge r11 v u) (a 10) (a 2) 0 t2 c11 (by decide +kernel)
  have t4 : a 10 ∈ [5] := remove (a 10) 0 [0,5] d10 b4
  have b5 : a 11 ≠ 0 := exclude [9] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t5 : a 11 ∈ [4] := remove (a 11) 0 [0,4] d11 b5
  have b6 : a 19 ≠ 0 := exclude [9] (fun u v => edge r15 v u) (a 19) (a 3) 0 t0 c15 (by decide +kernel)
  have t6 : a 19 ∈ [6] := remove (a 19) 0 [0,6] d19 b6
  have b7 : a 4 ≠ 0 := exclude [4] (edge r16) (a 4) (a 5) 0 t1 c16 (by decide +kernel)
  have t7 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b7
  have b8 : a 12 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 12) (a 4) 0 t7 c18 (by decide +kernel)
  have t8 : a 12 ∈ [20] := remove (a 12) 0 [0,20] d12 b8
  have b9 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t7 c19 (by decide +kernel)
  have t9 : a 20 ∈ [3] := remove (a 20) 0 [0,3] d20 b9
  have b10 : a 13 ≠ 0 := exclude [4] (fun u v => edge r21 v u) (a 13) (a 5) 0 t1 c21 (by decide +kernel)
  have t10 : a 13 ∈ [6] := remove (a 13) 0 [0,6] d13 b10
  have b11 : a 21 ≠ 0 := exclude [4] (fun u v => edge r22 v u) (a 21) (a 5) 0 t1 c22 (by decide +kernel)
  have t11 : a 21 ∈ [4] := remove (a 21) 0 [0,4] d21 b11
  have b12 : a 14 ≠ 0 := exclude [9] (fun u v => edge r24 v u) (a 14) (a 6) 0 t3 c24 (by decide +kernel)
  have t12 : a 14 ∈ [9] := remove (a 14) 0 [0,9] d14 b12
  have b13 : a 22 ≠ 0 := exclude [9] (fun u v => edge r25 v u) (a 22) (a 6) 0 t3 c25 (by decide +kernel)
  have t13 : a 22 ∈ [3] := remove (a 22) 0 [0,3] d22 b13
  have b14 : a 8 ≠ 0 := exclude [5] (edge r29) (a 8) (a 10) 0 t4 c29 (by decide +kernel)
  have t14 : a 8 ∈ [3] := remove (a 8) 0 [0,3] d8 b14
  have b15 : a 24 ≠ 0 := exclude [3] (fun u v => edge r31 v u) (a 24) (a 8) 0 t14 c31 (by decide +kernel)
  have t15 : a 24 ∈ [16] := remove (a 24) 0 [0,16] d24 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk27 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,12])
    (d10 : a 10 ∈ [5])
    (d15 : a 15 ∈ [0,21])
    (d11 : a 11 ∈ [4])
    (d29 : a 29 ∈ [0,18])
    (d13 : a 13 ∈ [6])
    (d30 : a 30 ∈ [0,5])
    (d14 : a 14 ∈ [9])
    (d31 : a 31 ∈ [0,18])
    (d16 : a 16 ∈ [0,5])
    (d20 : a 20 ∈ [3])
    (d18 : a 18 ∈ [0,13])
    (d19 : a 19 ∈ [6])
    (d23 : a 23 ∈ [0,12])
    (d25 : a 25 ∈ [0,18])
    (d24 : a 24 ∈ [16])
    (d27 : a 27 ∈ [0,3])
    (d9 : a 9 ∈ [0,5])
    (d8 : a 8 ∈ [3])
    (d17 : a 17 ∈ [0,3])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 26 ∈ [12] ∧ a 15 ∈ [21] ∧ a 29 ∈ [18] ∧ a 30 ∈ [5] ∧ a 31 ∈ [18] ∧ a 16 ∈ [5] ∧ a 18 ∈ [13] ∧ a 23 ∈ [12] ∧ a 25 ∈ [18] ∧ a 27 ∈ [3] ∧ a 9 ∈ [5] ∧ a 17 ∈ [3] := by
  have b0 : a 26 ≠ 0 := exclude [5] (fun u v => edge r37 v u) (a 26) (a 10) 0 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [12] := remove (a 26) 0 [0,12] d26 b0
  have b1 : a 15 ≠ 0 := exclude [4] (fun u v => edge r38 v u) (a 15) (a 11) 0 d11 c38 (by decide +kernel)
  have t1 : a 15 ∈ [21] := remove (a 15) 0 [0,21] d15 b1
  have b2 : a 29 ≠ 0 := exclude [6] (fun u v => edge r44 v u) (a 29) (a 13) 0 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [18] := remove (a 29) 0 [0,18] d29 b2
  have b3 : a 30 ≠ 0 := exclude [9] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [5] := remove (a 30) 0 [0,5] d30 b3
  have b4 : a 31 ≠ 0 := exclude [21] (fun u v => edge r47 v u) (a 31) (a 15) 0 t1 c47 (by decide +kernel)
  have t4 : a 31 ∈ [18] := remove (a 31) 0 [0,18] d31 b4
  have b5 : a 16 ≠ 0 := exclude [3] (edge r50) (a 16) (a 20) 0 d20 c50 (by decide +kernel)
  have t5 : a 16 ∈ [5] := remove (a 16) 0 [0,5] d16 b5
  have b6 : a 18 ≠ 0 := exclude [6] (edge r55) (a 18) (a 19) 0 d19 c55 (by decide +kernel)
  have t6 : a 18 ∈ [13] := remove (a 18) 0 [0,13] d18 b6
  have b7 : a 23 ≠ 0 := exclude [6] (fun u v => edge r58 v u) (a 23) (a 19) 0 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [12] := remove (a 23) 0 [0,12] d23 b7
  have b8 : a 25 ≠ 0 := exclude [16] (fun u v => edge r68 v u) (a 25) (a 24) 0 d24 c68 (by decide +kernel)
  have t8 : a 25 ∈ [18] := remove (a 25) 0 [0,18] d25 b8
  have b9 : a 27 ≠ 0 := exclude [12] (fun u v => edge r73 v u) (a 27) (a 26) 0 t0 c73 (by decide +kernel)
  have t9 : a 27 ∈ [3] := remove (a 27) 0 [0,3] d27 b9
  have b10 : a 9 ≠ 0 := exclude [3] (fun u v => edge r28 v u) (a 9) (a 8) 0 d8 c28 (by decide +kernel)
  have t10 : a 9 ∈ [5] := remove (a 9) 0 [0,5] d9 b10
  have b11 : a 17 ≠ 0 := exclude [5] (fun u v => edge r48 v u) (a 17) (a 16) 0 t5 c48 (by decide +kernel)
  have t11 : a 17 ∈ [3] := remove (a 17) 0 [0,3] d17 b11
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t11)))))))))))
#print axioms chunk24
#print axioms chunk25
#print axioms chunk26
#print axioms chunk27
end PartitionCover205_191
