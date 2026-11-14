import PartitionData205_194
namespace PartitionCover205_194
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,6,13])
    (d25 : a 25 ∈ [0,6])
    (d30 : a 30 ∈ [0,1,3,4])
    (d26 : a 26 ∈ [0,1])
    (d1 : a 1 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0,1,2,4])
    (d7 : a 7 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,2,4,6])
    (d13 : a 13 ∈ [0,4])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 29 ∈ [0,6] ∧ a 30 ∈ [0,3] ∧ a 1 ∈ [0,1] ∧ a 2 ∈ [0,1] ∧ a 7 ∈ [0,1] ∧ a 5 ∈ [0,4] := by
  have b0 : a 29 ≠ 13 := exclude [0,6] (fun u v => edge r72 v u) (a 29) (a 25) 13 d25 c72 (by decide +kernel)
  have t0 : a 29 ∈ [0,6] := remove (a 29) 13 [0,6,13] d29 b0
  have b1 : a 30 ≠ 1 := exclude [0,1] (fun u v => edge r74 v u) (a 30) (a 26) 1 d26 c74 (by decide +kernel)
  have t1 : a 30 ∈ [0,3,4] := remove (a 30) 1 [0,1,3,4] d30 b1
  have b2 : a 30 ≠ 4 := exclude [0,1] (fun u v => edge r74 v u) (a 30) (a 26) 4 d26 c74 (by decide +kernel)
  have t2 : a 30 ∈ [0,3] := remove (a 30) 4 [0,3,4] t1 b2
  have b3 : a 1 ≠ 2 := exclude [0,1] (edge r5) (a 1) (a 3) 2 d3 c5 (by decide +kernel)
  have t3 : a 1 ∈ [0,1,3] := remove (a 1) 2 [0,1,2,3] d1 b3
  have b4 : a 1 ≠ 3 := exclude [0,1] (edge r5) (a 1) (a 3) 3 d3 c5 (by decide +kernel)
  have t4 : a 1 ∈ [0,1] := remove (a 1) 3 [0,1,3] t3 b4
  have b5 : a 2 ≠ 2 := exclude [0,1] (edge r9) (a 2) (a 3) 2 d3 c9 (by decide +kernel)
  have t5 : a 2 ∈ [0,1,4] := remove (a 2) 2 [0,1,2,4] d2 b5
  have b6 : a 2 ≠ 4 := exclude [0,1] (edge r9) (a 2) (a 3) 4 d3 c9 (by decide +kernel)
  have t6 : a 2 ∈ [0,1] := remove (a 2) 4 [0,1,4] t5 b6
  have b7 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 7) (a 3) 2 d3 c13 (by decide +kernel)
  have t7 : a 7 ∈ [0,1] := remove (a 7) 2 [0,1,2] d7 b7
  have b8 : a 5 ≠ 2 := exclude [0,4] (edge r21) (a 5) (a 13) 2 d13 c21 (by decide +kernel)
  have t8 : a 5 ∈ [0,4,6] := remove (a 5) 2 [0,2,4,6] d5 b8
  have b9 : a 5 ≠ 6 := exclude [0,4] (edge r21) (a 5) (a 13) 6 d13 c21 (by decide +kernel)
  have t9 : a 5 ∈ [0,4] := remove (a 5) 6 [0,4,6] t8 b9
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (t9)))))

theorem chunk13 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,3])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,6])
    (d10 : a 10 ∈ [0,1])
    (d30 : a 30 ∈ [0,3])
    (d31 : a 31 ∈ [0,3])
    (d16 : a 16 ∈ [0,2])
    (d28 : a 28 ∈ [0,6])
    (d26 : a 26 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 3 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] ∧ a 20 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 10 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 28 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 1 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 2 ≠ 1 := exclude [0] (edge r9) (a 2) (a 3) 1 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b1
  have b2 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b2
  have b3 : a 7 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 1 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b3
  have b4 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t2 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b4
  have b5 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 t4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b5
  have b6 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 t2 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b6
  have b7 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 3 t2 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0] := remove (a 22) 3 [0,3] d22 b7
  have b8 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 t3 c26 (by decide +kernel)
  have t8 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b8
  have b9 : a 23 ≠ 6 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 6 t3 c27 (by decide +kernel)
  have t9 : a 23 ∈ [0] := remove (a 23) 6 [0,6] d23 b9
  have b10 : a 10 ≠ 1 := exclude [0] (edge r36) (a 10) (a 14) 1 t6 c36 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b10
  have b11 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 t6 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0] := remove (a 30) 3 [0,3] d30 b11
  have b12 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 t8 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0] := remove (a 31) 3 [0,3] d31 b12
  have b13 : a 16 ≠ 2 := exclude [0] (edge r50) (a 16) (a 20) 2 t5 c50 (by decide +kernel)
  have t13 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b13
  have b14 : a 28 ≠ 6 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 6 t5 c62 (by decide +kernel)
  have t14 : a 28 ∈ [0] := remove (a 28) 6 [0,6] d28 b14
  have b15 : a 26 ≠ 1 := exclude [0] (edge r74) (a 26) (a 30) 1 t11 c74 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk14 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,3])
    (d31 : a 31 ∈ [0])
    (d29 : a 29 ∈ [0,6])
    (d28 : a 28 ∈ [0])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d17 : a 17 ∈ [0,4])
    (d16 : a 16 ∈ [0])
    (d21 : a 21 ∈ [0,4])
    (d25 : a 25 ∈ [0,6])
    (d5 : a 5 ∈ [0,4])
    (d9 : a 9 ∈ [0,4])
    (d13 : a 13 ∈ [0,4])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 27 ∈ [0] ∧ a 29 ∈ [0] ∧ a 8 ∈ [0] ∧ a 17 ∈ [0] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 27 ≠ 3 := exclude [0] (edge r75) (a 27) (a 31) 3 d31 c75 (by decide +kernel)
  have t0 : a 27 ∈ [0] := remove (a 27) 3 [0,3] d27 b0
  have b1 : a 29 ≠ 6 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 6 d28 c76 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 6 [0,6] d29 b1
  have b2 : a 8 ≠ 1 := exclude [0] (edge r29) (a 8) (a 10) 1 d10 c29 (by decide +kernel)
  have t2 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b2
  have b3 : a 17 ≠ 4 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 4 d16 c48 (by decide +kernel)
  have t3 : a 17 ∈ [0] := remove (a 17) 4 [0,4] d17 b3
  have b4 : a 21 ≠ 4 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 4 t3 c53 (by decide +kernel)
  have t4 : a 21 ∈ [0] := remove (a 21) 4 [0,4] d21 b4
  have b5 : a 25 ≠ 6 := exclude [0] (edge r71) (a 25) (a 27) 6 t0 c71 (by decide +kernel)
  have t5 : a 25 ∈ [0] := remove (a 25) 6 [0,6] d25 b5
  have b6 : a 5 ≠ 4 := exclude [0] (edge r22) (a 5) (a 21) 4 t4 c22 (by decide +kernel)
  have t6 : a 5 ∈ [0] := remove (a 5) 4 [0,4] d5 b6
  have b7 : a 9 ≠ 4 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 4 t2 c28 (by decide +kernel)
  have t7 : a 9 ∈ [0] := remove (a 9) 4 [0,4] d9 b7
  have b8 : a 13 ≠ 4 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 4 t7 c33 (by decide +kernel)
  have t8 : a 13 ∈ [0] := remove (a 13) 4 [0,4] d13 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))

theorem chunk15 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,3])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,6])
    (d10 : a 10 ∈ [0,1])
    (d30 : a 30 ∈ [0,3])
    (d31 : a 31 ∈ [0,3])
    (d16 : a 16 ∈ [0,2])
    (d28 : a 28 ∈ [0,6])
    (d26 : a 26 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 3 ∈ [1] ∧ a 2 ∈ [1] ∧ a 6 ∈ [1] ∧ a 7 ∈ [1] ∧ a 4 ∈ [1] ∧ a 20 ∈ [2] ∧ a 14 ∈ [1] ∧ a 22 ∈ [3] ∧ a 15 ∈ [1] ∧ a 23 ∈ [6] ∧ a 10 ∈ [1] ∧ a 30 ∈ [3] ∧ a 31 ∈ [3] ∧ a 16 ∈ [2] ∧ a 28 ∈ [6] ∧ a 26 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 2 ≠ 0 := exclude [1] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b1
  have b2 : a 6 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 6) (a 2) 0 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b2
  have b3 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b3
  have b4 : a 4 ≠ 0 := exclude [1] (edge r17) (a 4) (a 6) 0 t2 c17 (by decide +kernel)
  have t4 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b4
  have b5 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [2] := remove (a 20) 0 [0,2] d20 b5
  have b6 : a 14 ≠ 0 := exclude [1] (fun u v => edge r24 v u) (a 14) (a 6) 0 t2 c24 (by decide +kernel)
  have t6 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b6
  have b7 : a 22 ≠ 0 := exclude [1] (fun u v => edge r25 v u) (a 22) (a 6) 0 t2 c25 (by decide +kernel)
  have t7 : a 22 ∈ [3] := remove (a 22) 0 [0,3] d22 b7
  have b8 : a 15 ≠ 0 := exclude [1] (fun u v => edge r26 v u) (a 15) (a 7) 0 t3 c26 (by decide +kernel)
  have t8 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b8
  have b9 : a 23 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 23) (a 7) 0 t3 c27 (by decide +kernel)
  have t9 : a 23 ∈ [6] := remove (a 23) 0 [0,6] d23 b9
  have b10 : a 10 ≠ 0 := exclude [1] (edge r36) (a 10) (a 14) 0 t6 c36 (by decide +kernel)
  have t10 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b10
  have b11 : a 30 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 30) (a 14) 0 t6 c46 (by decide +kernel)
  have t11 : a 30 ∈ [3] := remove (a 30) 0 [0,3] d30 b11
  have b12 : a 31 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 31) (a 15) 0 t8 c47 (by decide +kernel)
  have t12 : a 31 ∈ [3] := remove (a 31) 0 [0,3] d31 b12
  have b13 : a 16 ≠ 0 := exclude [2] (edge r50) (a 16) (a 20) 0 t5 c50 (by decide +kernel)
  have t13 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b13
  have b14 : a 28 ≠ 0 := exclude [2] (fun u v => edge r62 v u) (a 28) (a 20) 0 t5 c62 (by decide +kernel)
  have t14 : a 28 ∈ [6] := remove (a 28) 0 [0,6] d28 b14
  have b15 : a 26 ≠ 0 := exclude [3] (edge r74) (a 26) (a 30) 0 t11 c74 (by decide +kernel)
  have t15 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_194
