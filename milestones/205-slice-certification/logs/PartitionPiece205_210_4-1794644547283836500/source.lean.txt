import PartitionData205_210
namespace PartitionCover205_210
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,3])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (d2 : a 2 ∈ [0,6])
    (d6 : a 6 ∈ [0,4])
    (d10 : a 10 ∈ [0,2])
    (d18 : a 18 ∈ [0,12])
    (d7 : a 7 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,6])
    (d12 : a 12 ∈ [0,12])
    (d20 : a 20 ∈ [0,4])
    (d21 : a 21 ∈ [0,2])
    (d14 : a 14 ∈ [0,13])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] := by
  have b0 : a 3 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 3 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 3 [0,3] d3 b0
  have b1 : a 5 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b1
  have b2 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b2
  have b3 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b3
  have b4 : a 2 ≠ 6 := exclude [0] (edge r9) (a 2) (a 3) 6 t0 c9 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 6 [0,6] d2 b4
  have b5 : a 6 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 4 t4 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b5
  have b6 : a 10 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 2 t4 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b6
  have b7 : a 18 ≠ 12 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 12 t4 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0] := remove (a 18) 12 [0,12] d18 b7
  have b8 : a 7 ≠ 2 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 2 t0 c13 (by decide +kernel)
  have t8 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b8
  have b9 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 t0 c14 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b9
  have b10 : a 19 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 6 t0 c15 (by decide +kernel)
  have t10 : a 19 ∈ [0] := remove (a 19) 6 [0,6] d19 b10
  have b11 : a 4 ≠ 6 := exclude [0] (edge r16) (a 4) (a 5) 6 t1 c16 (by decide +kernel)
  have t11 : a 4 ∈ [0] := remove (a 4) 6 [0,6] d4 b11
  have b12 : a 12 ≠ 12 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 12 t11 c18 (by decide +kernel)
  have t12 : a 12 ∈ [0] := remove (a 12) 12 [0,12] d12 b12
  have b13 : a 20 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 4 t11 c19 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 4 [0,4] d20 b13
  have b14 : a 21 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 2 t1 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b14
  have b15 : a 14 ≠ 13 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 13 t5 c24 (by decide +kernel)
  have t15 : a 14 ∈ [0] := remove (a 14) 13 [0,13] d14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk17 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,9])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d7 : a 7 ∈ [0])
    (d23 : a 23 ∈ [0,4])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d24 : a 24 ∈ [0,8])
    (d26 : a 26 ∈ [0,8])
    (d10 : a 10 ∈ [0])
    (d27 : a 27 ∈ [0,4])
    (d11 : a 11 ∈ [0])
    (d13 : a 13 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d28 : a 28 ∈ [0,14])
    (d29 : a 29 ∈ [0,4])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,4])
    (d16 : a 16 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d25 : a 25 ∈ [0,8])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 13 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 25 ∈ [0] := by
  have b0 : a 22 ≠ 9 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [0] := remove (a 22) 9 [0,9] d22 b0
  have b1 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b1
  have b2 : a 23 ≠ 4 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t2 : a 23 ∈ [0] := remove (a 23) 4 [0,4] d23 b2
  have b3 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t3 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b3
  have b4 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 t3 c31 (by decide +kernel)
  have t4 : a 24 ∈ [0] := remove (a 24) 8 [0,8] d24 b4
  have b5 : a 26 ≠ 8 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 8 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0] := remove (a 26) 8 [0,8] d26 b5
  have b6 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [0] := remove (a 27) 4 [0,4] d27 b6
  have b7 : a 13 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 1 d12 c40 (by decide +kernel)
  have t7 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b7
  have b8 : a 28 ≠ 14 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 14 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0] := remove (a 28) 14 [0,14] d28 b8
  have b9 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 t7 c44 (by decide +kernel)
  have t9 : a 29 ∈ [0] := remove (a 29) 4 [0,4] d29 b9
  have b10 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b10
  have b11 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 t1 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0] := remove (a 31) 4 [0,4] d31 b11
  have b12 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 17) 1 d17 c48 (by decide +kernel)
  have t12 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b12
  have b13 : a 25 ≠ 8 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 8 t4 c68 (by decide +kernel)
  have t13 : a 25 ∈ [0] := remove (a 25) 8 [0,8] d25 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

theorem chunk18 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,3])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (d2 : a 2 ∈ [0,6])
    (d6 : a 6 ∈ [0,4])
    (d10 : a 10 ∈ [0,2])
    (d18 : a 18 ∈ [0,12])
    (d7 : a 7 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,6])
    (d12 : a 12 ∈ [0,12])
    (d20 : a 20 ∈ [0,4])
    (d21 : a 21 ∈ [0,2])
    (d14 : a 14 ∈ [0,13])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    : a 3 ∈ [3] ∧ a 5 ∈ [2] ∧ a 9 ∈ [1] ∧ a 17 ∈ [2] ∧ a 2 ∈ [6] ∧ a 6 ∈ [4] ∧ a 10 ∈ [2] ∧ a 18 ∈ [12] ∧ a 7 ∈ [2] ∧ a 11 ∈ [2] ∧ a 19 ∈ [6] ∧ a 4 ∈ [6] ∧ a 12 ∈ [12] ∧ a 20 ∈ [4] ∧ a 21 ∈ [2] ∧ a 14 ∈ [13] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [3] := remove (a 3) 0 [0,3] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 5) (a 1) 0 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b1
  have b2 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b2
  have b3 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [2] := remove (a 17) 0 [0,2] d17 b3
  have b4 : a 2 ≠ 0 := exclude [3] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t4 : a 2 ∈ [6] := remove (a 2) 0 [0,6] d2 b4
  have b5 : a 6 ≠ 0 := exclude [6] (fun u v => edge r10 v u) (a 6) (a 2) 0 t4 c10 (by decide +kernel)
  have t5 : a 6 ∈ [4] := remove (a 6) 0 [0,4] d6 b5
  have b6 : a 10 ≠ 0 := exclude [6] (fun u v => edge r11 v u) (a 10) (a 2) 0 t4 c11 (by decide +kernel)
  have t6 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b6
  have b7 : a 18 ≠ 0 := exclude [6] (fun u v => edge r12 v u) (a 18) (a 2) 0 t4 c12 (by decide +kernel)
  have t7 : a 18 ∈ [12] := remove (a 18) 0 [0,12] d18 b7
  have b8 : a 7 ≠ 0 := exclude [3] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t8 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b8
  have b9 : a 11 ≠ 0 := exclude [3] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t9 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b9
  have b10 : a 19 ≠ 0 := exclude [3] (fun u v => edge r15 v u) (a 19) (a 3) 0 t0 c15 (by decide +kernel)
  have t10 : a 19 ∈ [6] := remove (a 19) 0 [0,6] d19 b10
  have b11 : a 4 ≠ 0 := exclude [2] (edge r16) (a 4) (a 5) 0 t1 c16 (by decide +kernel)
  have t11 : a 4 ∈ [6] := remove (a 4) 0 [0,6] d4 b11
  have b12 : a 12 ≠ 0 := exclude [6] (fun u v => edge r18 v u) (a 12) (a 4) 0 t11 c18 (by decide +kernel)
  have t12 : a 12 ∈ [12] := remove (a 12) 0 [0,12] d12 b12
  have b13 : a 20 ≠ 0 := exclude [6] (fun u v => edge r19 v u) (a 20) (a 4) 0 t11 c19 (by decide +kernel)
  have t13 : a 20 ∈ [4] := remove (a 20) 0 [0,4] d20 b13
  have b14 : a 21 ≠ 0 := exclude [2] (fun u v => edge r22 v u) (a 21) (a 5) 0 t1 c22 (by decide +kernel)
  have t14 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b14
  have b15 : a 14 ≠ 0 := exclude [4] (fun u v => edge r24 v u) (a 14) (a 6) 0 t5 c24 (by decide +kernel)
  have t15 : a 14 ∈ [13] := remove (a 14) 0 [0,13] d14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk19 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,9])
    (d6 : a 6 ∈ [4])
    (d15 : a 15 ∈ [0,1])
    (d7 : a 7 ∈ [2])
    (d23 : a 23 ∈ [0,4])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [1])
    (d24 : a 24 ∈ [0,8])
    (d26 : a 26 ∈ [0,8])
    (d10 : a 10 ∈ [2])
    (d27 : a 27 ∈ [0,4])
    (d11 : a 11 ∈ [2])
    (d13 : a 13 ∈ [0,1])
    (d12 : a 12 ∈ [12])
    (d28 : a 28 ∈ [0,14])
    (d29 : a 29 ∈ [0,4])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [13])
    (d31 : a 31 ∈ [0,4])
    (d16 : a 16 ∈ [0,1])
    (d17 : a 17 ∈ [2])
    (d25 : a 25 ∈ [0,8])
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 22 ∈ [9] ∧ a 15 ∈ [1] ∧ a 23 ∈ [4] ∧ a 8 ∈ [1] ∧ a 24 ∈ [8] ∧ a 26 ∈ [8] ∧ a 27 ∈ [4] ∧ a 13 ∈ [1] ∧ a 28 ∈ [14] ∧ a 29 ∈ [4] ∧ a 30 ∈ [1] ∧ a 31 ∈ [4] ∧ a 16 ∈ [1] ∧ a 25 ∈ [8] := by
  have b0 : a 22 ≠ 0 := exclude [4] (fun u v => edge r25 v u) (a 22) (a 6) 0 d6 c25 (by decide +kernel)
  have t0 : a 22 ∈ [9] := remove (a 22) 0 [0,9] d22 b0
  have b1 : a 15 ≠ 0 := exclude [2] (fun u v => edge r26 v u) (a 15) (a 7) 0 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b1
  have b2 : a 23 ≠ 0 := exclude [2] (fun u v => edge r27 v u) (a 23) (a 7) 0 d7 c27 (by decide +kernel)
  have t2 : a 23 ∈ [4] := remove (a 23) 0 [0,4] d23 b2
  have b3 : a 8 ≠ 0 := exclude [1] (edge r28) (a 8) (a 9) 0 d9 c28 (by decide +kernel)
  have t3 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b3
  have b4 : a 24 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 24) (a 8) 0 t3 c31 (by decide +kernel)
  have t4 : a 24 ∈ [8] := remove (a 24) 0 [0,8] d24 b4
  have b5 : a 26 ≠ 0 := exclude [2] (fun u v => edge r37 v u) (a 26) (a 10) 0 d10 c37 (by decide +kernel)
  have t5 : a 26 ∈ [8] := remove (a 26) 0 [0,8] d26 b5
  have b6 : a 27 ≠ 0 := exclude [2] (fun u v => edge r39 v u) (a 27) (a 11) 0 d11 c39 (by decide +kernel)
  have t6 : a 27 ∈ [4] := remove (a 27) 0 [0,4] d27 b6
  have b7 : a 13 ≠ 0 := exclude [12] (fun u v => edge r40 v u) (a 13) (a 12) 0 d12 c40 (by decide +kernel)
  have t7 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b7
  have b8 : a 28 ≠ 0 := exclude [12] (fun u v => edge r42 v u) (a 28) (a 12) 0 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [14] := remove (a 28) 0 [0,14] d28 b8
  have b9 : a 29 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 29) (a 13) 0 t7 c44 (by decide +kernel)
  have t9 : a 29 ∈ [4] := remove (a 29) 0 [0,4] d29 b9
  have b10 : a 30 ≠ 0 := exclude [13] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b10
  have b11 : a 31 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 31) (a 15) 0 t1 c47 (by decide +kernel)
  have t11 : a 31 ∈ [4] := remove (a 31) 0 [0,4] d31 b11
  have b12 : a 16 ≠ 0 := exclude [2] (edge r48) (a 16) (a 17) 0 d17 c48 (by decide +kernel)
  have t12 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b12
  have b13 : a 25 ≠ 0 := exclude [8] (fun u v => edge r68 v u) (a 25) (a 24) 0 t4 c68 (by decide +kernel)
  have t13 : a 25 ∈ [8] := remove (a 25) 0 [0,8] d25 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_210
