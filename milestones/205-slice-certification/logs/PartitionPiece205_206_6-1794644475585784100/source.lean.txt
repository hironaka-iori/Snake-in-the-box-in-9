import PartitionData205_206
namespace PartitionCover205_206
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,2])
    (d17 : a 17 ∈ [0,4])
    (d4 : a 4 ∈ [0,6])
    (d6 : a 6 ∈ [0,4])
    (d12 : a 12 ∈ [0,12])
    (d20 : a 20 ∈ [0,6])
    (d7 : a 7 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d14 : a 14 ∈ [0,12])
    (d22 : a 22 ∈ [0,6])
    (d15 : a 15 ∈ [0,4])
    (d23 : a 23 ∈ [0,4])
    (d8 : a 8 ∈ [0,6])
    (d10 : a 10 ∈ [0,4])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    : a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 7 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] := by
  have b0 : a 5 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b0
  have b1 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b1
  have b2 : a 17 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 4 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 4 [0,4] d17 b2
  have b3 : a 4 ≠ 6 := exclude [0] (edge r16) (a 4) (a 5) 6 t0 c16 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 6 [0,6] d4 b3
  have b4 : a 6 ≠ 4 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 4 t3 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b4
  have b5 : a 12 ≠ 12 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 12 t3 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 12 [0,12] d12 b5
  have b6 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 t3 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0] := remove (a 20) 6 [0,6] d20 b6
  have b7 : a 7 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 2 t0 c20 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b7
  have b8 : a 13 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 1 t0 c21 (by decide +kernel)
  have t8 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b8
  have b9 : a 21 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 2 t0 c22 (by decide +kernel)
  have t9 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b9
  have b10 : a 14 ≠ 12 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 12 t4 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0] := remove (a 14) 12 [0,12] d14 b10
  have b11 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 t4 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0] := remove (a 22) 6 [0,6] d22 b11
  have b12 : a 15 ≠ 4 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 4 t7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0] := remove (a 15) 4 [0,4] d15 b12
  have b13 : a 23 ≠ 4 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 4 t7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0] := remove (a 23) 4 [0,4] d23 b13
  have b14 : a 8 ≠ 6 := exclude [0] (edge r28) (a 8) (a 9) 6 t1 c28 (by decide +kernel)
  have t14 : a 8 ∈ [0] := remove (a 8) 6 [0,6] d8 b14
  have b15 : a 10 ≠ 4 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 4 t14 c29 (by decide +kernel)
  have t15 : a 10 ∈ [0] := remove (a 10) 4 [0,4] d10 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk25 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,18])
    (d8 : a 8 ∈ [0])
    (d11 : a 11 ∈ [0,4])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,9])
    (d26 : a 26 ∈ [0,8])
    (d10 : a 10 ∈ [0])
    (d27 : a 27 ∈ [0,2])
    (d28 : a 28 ∈ [0,9])
    (d12 : a 12 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d16 : a 16 ∈ [0,8])
    (d17 : a 17 ∈ [0])
    (d18 : a 18 ∈ [0,4])
    (d19 : a 19 ∈ [0,1])
    (d29 : a 29 ∈ [0,18])
    (d31 : a 31 ∈ [0,1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0])
    (d3 : a 3 ∈ [0,1])
    (d7 : a 7 ∈ [0])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 24 ∈ [0] ∧ a 11 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 30 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0] ∧ a 29 ∈ [0] ∧ a 31 ∈ [0] ∧ a 2 ∈ [0] ∧ a 3 ∈ [0] := by
  have b0 : a 24 ≠ 18 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 18 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0] := remove (a 24) 18 [0,18] d24 b0
  have b1 : a 11 ≠ 4 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 4 d9 c32 (by decide +kernel)
  have t1 : a 11 ∈ [0] := remove (a 11) 4 [0,4] d11 b1
  have b2 : a 25 ≠ 9 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 9 [0,9] d25 b2
  have b3 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0] := remove (a 26) 8 [0,8] d26 b3
  have b4 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 t1 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b4
  have b5 : a 28 ≠ 9 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 9 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0] := remove (a 28) 9 [0,9] d28 b5
  have b6 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b6
  have b7 : a 16 ≠ 8 := exclude [0] (edge r48) (a 16) (a 17) 8 d17 c48 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 8 [0,8] d16 b7
  have b8 : a 18 ≠ 4 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 4 t7 c49 (by decide +kernel)
  have t8 : a 18 ∈ [0] := remove (a 18) 4 [0,4] d18 b8
  have b9 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t9 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b9
  have b10 : a 29 ≠ 18 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 18 t2 c72 (by decide +kernel)
  have t10 : a 29 ∈ [0] := remove (a 29) 18 [0,18] d29 b10
  have b11 : a 31 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 1 t4 c75 (by decide +kernel)
  have t11 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b11
  have b12 : a 2 ≠ 2 := exclude [0] (edge r10) (a 2) (a 6) 2 d6 c10 (by decide +kernel)
  have t12 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b12
  have b13 : a 3 ≠ 1 := exclude [0] (edge r13) (a 3) (a 7) 1 d7 c13 (by decide +kernel)
  have t13 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

theorem chunk26 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,2])
    (d1 : a 1 ∈ [1])
    (d9 : a 9 ∈ [0,2])
    (d17 : a 17 ∈ [0,4])
    (d4 : a 4 ∈ [0,6])
    (d6 : a 6 ∈ [0,4])
    (d12 : a 12 ∈ [0,12])
    (d20 : a 20 ∈ [0,6])
    (d7 : a 7 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d14 : a 14 ∈ [0,12])
    (d22 : a 22 ∈ [0,6])
    (d15 : a 15 ∈ [0,4])
    (d23 : a 23 ∈ [0,4])
    (d8 : a 8 ∈ [0,6])
    (d10 : a 10 ∈ [0,4])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    : a 5 ∈ [2] ∧ a 9 ∈ [2] ∧ a 17 ∈ [4] ∧ a 4 ∈ [6] ∧ a 6 ∈ [4] ∧ a 12 ∈ [12] ∧ a 20 ∈ [6] ∧ a 7 ∈ [2] ∧ a 13 ∈ [1] ∧ a 21 ∈ [2] ∧ a 14 ∈ [12] ∧ a 22 ∈ [6] ∧ a 15 ∈ [4] ∧ a 23 ∈ [4] ∧ a 8 ∈ [6] ∧ a 10 ∈ [4] := by
  have b0 : a 5 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 5) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b0
  have b1 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b1
  have b2 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [4] := remove (a 17) 0 [0,4] d17 b2
  have b3 : a 4 ≠ 0 := exclude [2] (edge r16) (a 4) (a 5) 0 t0 c16 (by decide +kernel)
  have t3 : a 4 ∈ [6] := remove (a 4) 0 [0,6] d4 b3
  have b4 : a 6 ≠ 0 := exclude [6] (fun u v => edge r17 v u) (a 6) (a 4) 0 t3 c17 (by decide +kernel)
  have t4 : a 6 ∈ [4] := remove (a 6) 0 [0,4] d6 b4
  have b5 : a 12 ≠ 0 := exclude [6] (fun u v => edge r18 v u) (a 12) (a 4) 0 t3 c18 (by decide +kernel)
  have t5 : a 12 ∈ [12] := remove (a 12) 0 [0,12] d12 b5
  have b6 : a 20 ≠ 0 := exclude [6] (fun u v => edge r19 v u) (a 20) (a 4) 0 t3 c19 (by decide +kernel)
  have t6 : a 20 ∈ [6] := remove (a 20) 0 [0,6] d20 b6
  have b7 : a 7 ≠ 0 := exclude [2] (fun u v => edge r20 v u) (a 7) (a 5) 0 t0 c20 (by decide +kernel)
  have t7 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b7
  have b8 : a 13 ≠ 0 := exclude [2] (fun u v => edge r21 v u) (a 13) (a 5) 0 t0 c21 (by decide +kernel)
  have t8 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b8
  have b9 : a 21 ≠ 0 := exclude [2] (fun u v => edge r22 v u) (a 21) (a 5) 0 t0 c22 (by decide +kernel)
  have t9 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b9
  have b10 : a 14 ≠ 0 := exclude [4] (fun u v => edge r24 v u) (a 14) (a 6) 0 t4 c24 (by decide +kernel)
  have t10 : a 14 ∈ [12] := remove (a 14) 0 [0,12] d14 b10
  have b11 : a 22 ≠ 0 := exclude [4] (fun u v => edge r25 v u) (a 22) (a 6) 0 t4 c25 (by decide +kernel)
  have t11 : a 22 ∈ [6] := remove (a 22) 0 [0,6] d22 b11
  have b12 : a 15 ≠ 0 := exclude [2] (fun u v => edge r26 v u) (a 15) (a 7) 0 t7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [4] := remove (a 15) 0 [0,4] d15 b12
  have b13 : a 23 ≠ 0 := exclude [2] (fun u v => edge r27 v u) (a 23) (a 7) 0 t7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [4] := remove (a 23) 0 [0,4] d23 b13
  have b14 : a 8 ≠ 0 := exclude [2] (edge r28) (a 8) (a 9) 0 t1 c28 (by decide +kernel)
  have t14 : a 8 ∈ [6] := remove (a 8) 0 [0,6] d8 b14
  have b15 : a 10 ≠ 0 := exclude [6] (fun u v => edge r29 v u) (a 10) (a 8) 0 t14 c29 (by decide +kernel)
  have t15 : a 10 ∈ [4] := remove (a 10) 0 [0,4] d10 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk27 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,18])
    (d8 : a 8 ∈ [6])
    (d11 : a 11 ∈ [0,4])
    (d9 : a 9 ∈ [2])
    (d25 : a 25 ∈ [0,9])
    (d26 : a 26 ∈ [0,8])
    (d10 : a 10 ∈ [4])
    (d27 : a 27 ∈ [0,2])
    (d28 : a 28 ∈ [0,9])
    (d12 : a 12 ∈ [12])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [12])
    (d16 : a 16 ∈ [0,8])
    (d17 : a 17 ∈ [4])
    (d18 : a 18 ∈ [0,4])
    (d19 : a 19 ∈ [0,1])
    (d29 : a 29 ∈ [0,18])
    (d31 : a 31 ∈ [0,1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [4])
    (d3 : a 3 ∈ [0,1])
    (d7 : a 7 ∈ [2])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 24 ∈ [18] ∧ a 11 ∈ [4] ∧ a 25 ∈ [9] ∧ a 26 ∈ [8] ∧ a 27 ∈ [2] ∧ a 28 ∈ [9] ∧ a 30 ∈ [1] ∧ a 16 ∈ [8] ∧ a 18 ∈ [4] ∧ a 19 ∈ [1] ∧ a 29 ∈ [18] ∧ a 31 ∈ [1] ∧ a 2 ∈ [2] ∧ a 3 ∈ [1] := by
  have b0 : a 24 ≠ 0 := exclude [6] (fun u v => edge r31 v u) (a 24) (a 8) 0 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [18] := remove (a 24) 0 [0,18] d24 b0
  have b1 : a 11 ≠ 0 := exclude [2] (fun u v => edge r32 v u) (a 11) (a 9) 0 d9 c32 (by decide +kernel)
  have t1 : a 11 ∈ [4] := remove (a 11) 0 [0,4] d11 b1
  have b2 : a 25 ≠ 0 := exclude [2] (fun u v => edge r34 v u) (a 25) (a 9) 0 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [9] := remove (a 25) 0 [0,9] d25 b2
  have b3 : a 26 ≠ 0 := exclude [4] (fun u v => edge r37 v u) (a 26) (a 10) 0 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [8] := remove (a 26) 0 [0,8] d26 b3
  have b4 : a 27 ≠ 0 := exclude [4] (fun u v => edge r39 v u) (a 27) (a 11) 0 t1 c39 (by decide +kernel)
  have t4 : a 27 ∈ [2] := remove (a 27) 0 [0,2] d27 b4
  have b5 : a 28 ≠ 0 := exclude [12] (fun u v => edge r42 v u) (a 28) (a 12) 0 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [9] := remove (a 28) 0 [0,9] d28 b5
  have b6 : a 30 ≠ 0 := exclude [12] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b6
  have b7 : a 16 ≠ 0 := exclude [4] (edge r48) (a 16) (a 17) 0 d17 c48 (by decide +kernel)
  have t7 : a 16 ∈ [8] := remove (a 16) 0 [0,8] d16 b7
  have b8 : a 18 ≠ 0 := exclude [8] (fun u v => edge r49 v u) (a 18) (a 16) 0 t7 c49 (by decide +kernel)
  have t8 : a 18 ∈ [4] := remove (a 18) 0 [0,4] d18 b8
  have b9 : a 19 ≠ 0 := exclude [4] (fun u v => edge r52 v u) (a 19) (a 17) 0 d17 c52 (by decide +kernel)
  have t9 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b9
  have b10 : a 29 ≠ 0 := exclude [9] (fun u v => edge r72 v u) (a 29) (a 25) 0 t2 c72 (by decide +kernel)
  have t10 : a 29 ∈ [18] := remove (a 29) 0 [0,18] d29 b10
  have b11 : a 31 ≠ 0 := exclude [2] (fun u v => edge r75 v u) (a 31) (a 27) 0 t4 c75 (by decide +kernel)
  have t11 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b11
  have b12 : a 2 ≠ 0 := exclude [4] (edge r10) (a 2) (a 6) 0 d6 c10 (by decide +kernel)
  have t12 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b12
  have b13 : a 3 ≠ 0 := exclude [2] (edge r13) (a 3) (a 7) 0 d7 c13 (by decide +kernel)
  have t13 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
#print axioms chunk24
#print axioms chunk25
#print axioms chunk26
#print axioms chunk27
end PartitionCover205_206
