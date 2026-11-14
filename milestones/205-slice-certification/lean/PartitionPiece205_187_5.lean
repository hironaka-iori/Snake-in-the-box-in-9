import PartitionData205_187
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,20,22])
    (d4 : a 4 ∈ [0,9])
    (c16 : edge r16 (a 4) (a 5)=true)
    : a 5 ∈ [0,20] := by
  have b0 : a 5 ≠ 22 := exclude [0,9] (fun u v => edge r16 v u) (a 5) (a 4) 22 d4 c16 (by decide +kernel)
  have t0 : a 5 ∈ [0,20] := remove (a 5) 22 [0,20,22] d5 b0
  exact t0

theorem chunk21 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,6])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,20])
    (d9 : a 9 ∈ [0,2])
    (d17 : a 17 ∈ [0,3])
    (d7 : a 7 ∈ [0,3])
    (d11 : a 11 ∈ [0,6])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,9])
    (d6 : a 6 ∈ [0,8])
    (d12 : a 12 ∈ [0,2])
    (d20 : a 20 ∈ [0,9])
    (d14 : a 14 ∈ [0,2])
    (d22 : a 22 ∈ [0,11])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,2])
    (d24 : a 24 ∈ [0,9])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 24 ∈ [0] := by
  have b0 : a 3 ≠ 6 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 6 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 6 [0,6] d3 b0
  have b1 : a 5 ≠ 20 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 20 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 20 [0,20] d5 b1
  have b2 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b2
  have b3 : a 17 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 3 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0] := remove (a 17) 3 [0,3] d17 b3
  have b4 : a 7 ≠ 3 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 3 t0 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 3 [0,3] d7 b4
  have b5 : a 11 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 6 t0 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b5
  have b6 : a 19 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 6 t0 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 6 [0,6] d19 b6
  have b7 : a 4 ≠ 9 := exclude [0] (edge r16) (a 4) (a 5) 9 t1 c16 (by decide +kernel)
  have t7 : a 4 ∈ [0] := remove (a 4) 9 [0,9] d4 b7
  have b8 : a 6 ≠ 8 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 8 t7 c17 (by decide +kernel)
  have t8 : a 6 ∈ [0] := remove (a 6) 8 [0,8] d6 b8
  have b9 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 t7 c18 (by decide +kernel)
  have t9 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b9
  have b10 : a 20 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 9 t7 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0] := remove (a 20) 9 [0,9] d20 b10
  have b11 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 t8 c24 (by decide +kernel)
  have t11 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b11
  have b12 : a 22 ≠ 11 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 11 t8 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0] := remove (a 22) 11 [0,11] d22 b12
  have b13 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 t2 c28 (by decide +kernel)
  have t13 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b13
  have b14 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 t13 c29 (by decide +kernel)
  have t14 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b14
  have b15 : a 24 ≠ 9 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 9 t13 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0] := remove (a 24) 9 [0,9] d24 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk22 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,10])
    (d9 : a 9 ∈ [0])
    (d26 : a 26 ∈ [0,5])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,8])
    (d13 : a 13 ∈ [0,4])
    (d12 : a 12 ∈ [0])
    (d28 : a 28 ∈ [0,4])
    (d30 : a 30 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,5])
    (d16 : a 16 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d18 : a 18 ∈ [0,12])
    (d19 : a 19 ∈ [0])
    (d23 : a 23 ∈ [0,9])
    (d21 : a 21 ∈ [0,18])
    (d20 : a 20 ∈ [0])
    (d29 : a 29 ∈ [0,10])
    (d2 : a 2 ∈ [0,8])
    (d6 : a 6 ∈ [0])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0] ∧ a 13 ∈ [0] ∧ a 28 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 23 ∈ [0] ∧ a 21 ∈ [0] ∧ a 29 ∈ [0] ∧ a 2 ∈ [0] := by
  have b0 : a 25 ≠ 10 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0] := remove (a 25) 10 [0,10] d25 b0
  have b1 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0] := remove (a 26) 5 [0,5] d26 b1
  have b2 : a 15 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b2
  have b3 : a 27 ≠ 8 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0] := remove (a 27) 8 [0,8] d27 b3
  have b4 : a 13 ≠ 4 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 4 d12 c40 (by decide +kernel)
  have t4 : a 13 ∈ [0] := remove (a 13) 4 [0,4] d13 b4
  have b5 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [0] := remove (a 28) 4 [0,4] d28 b5
  have b6 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b6
  have b7 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 t2 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0] := remove (a 31) 5 [0,5] d31 b7
  have b8 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 17) 1 d17 c48 (by decide +kernel)
  have t8 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b8
  have b9 : a 18 ≠ 12 := exclude [0] (edge r55) (a 18) (a 19) 12 d19 c55 (by decide +kernel)
  have t9 : a 18 ∈ [0] := remove (a 18) 12 [0,12] d18 b9
  have b10 : a 23 ≠ 9 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 9 d19 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 9 [0,9] d23 b10
  have b11 : a 21 ≠ 18 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 18 d20 c60 (by decide +kernel)
  have t11 : a 21 ∈ [0] := remove (a 21) 18 [0,18] d21 b11
  have b12 : a 29 ≠ 10 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 10 t0 c72 (by decide +kernel)
  have t12 : a 29 ∈ [0] := remove (a 29) 10 [0,10] d29 b12
  have b13 : a 2 ≠ 8 := exclude [0] (edge r10) (a 2) (a 6) 8 d6 c10 (by decide +kernel)
  have t13 : a 2 ∈ [0] := remove (a 2) 8 [0,8] d2 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

theorem chunk23 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,6])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,20])
    (d9 : a 9 ∈ [0,2])
    (d17 : a 17 ∈ [0,3])
    (d7 : a 7 ∈ [0,3])
    (d11 : a 11 ∈ [0,6])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,9])
    (d6 : a 6 ∈ [0,8])
    (d12 : a 12 ∈ [0,2])
    (d20 : a 20 ∈ [0,9])
    (d14 : a 14 ∈ [0,2])
    (d22 : a 22 ∈ [0,11])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,2])
    (d24 : a 24 ∈ [0,9])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 3 ∈ [6] ∧ a 5 ∈ [20] ∧ a 9 ∈ [2] ∧ a 17 ∈ [3] ∧ a 7 ∈ [3] ∧ a 11 ∈ [6] ∧ a 19 ∈ [6] ∧ a 4 ∈ [9] ∧ a 6 ∈ [8] ∧ a 12 ∈ [2] ∧ a 20 ∈ [9] ∧ a 14 ∈ [2] ∧ a 22 ∈ [11] ∧ a 8 ∈ [1] ∧ a 10 ∈ [2] ∧ a 24 ∈ [9] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [6] := remove (a 3) 0 [0,6] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 5) (a 1) 0 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [20] := remove (a 5) 0 [0,20] d5 b1
  have b2 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b2
  have b3 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [3] := remove (a 17) 0 [0,3] d17 b3
  have b4 : a 7 ≠ 0 := exclude [6] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t4 : a 7 ∈ [3] := remove (a 7) 0 [0,3] d7 b4
  have b5 : a 11 ≠ 0 := exclude [6] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t5 : a 11 ∈ [6] := remove (a 11) 0 [0,6] d11 b5
  have b6 : a 19 ≠ 0 := exclude [6] (fun u v => edge r15 v u) (a 19) (a 3) 0 t0 c15 (by decide +kernel)
  have t6 : a 19 ∈ [6] := remove (a 19) 0 [0,6] d19 b6
  have b7 : a 4 ≠ 0 := exclude [20] (edge r16) (a 4) (a 5) 0 t1 c16 (by decide +kernel)
  have t7 : a 4 ∈ [9] := remove (a 4) 0 [0,9] d4 b7
  have b8 : a 6 ≠ 0 := exclude [9] (fun u v => edge r17 v u) (a 6) (a 4) 0 t7 c17 (by decide +kernel)
  have t8 : a 6 ∈ [8] := remove (a 6) 0 [0,8] d6 b8
  have b9 : a 12 ≠ 0 := exclude [9] (fun u v => edge r18 v u) (a 12) (a 4) 0 t7 c18 (by decide +kernel)
  have t9 : a 12 ∈ [2] := remove (a 12) 0 [0,2] d12 b9
  have b10 : a 20 ≠ 0 := exclude [9] (fun u v => edge r19 v u) (a 20) (a 4) 0 t7 c19 (by decide +kernel)
  have t10 : a 20 ∈ [9] := remove (a 20) 0 [0,9] d20 b10
  have b11 : a 14 ≠ 0 := exclude [8] (fun u v => edge r24 v u) (a 14) (a 6) 0 t8 c24 (by decide +kernel)
  have t11 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b11
  have b12 : a 22 ≠ 0 := exclude [8] (fun u v => edge r25 v u) (a 22) (a 6) 0 t8 c25 (by decide +kernel)
  have t12 : a 22 ∈ [11] := remove (a 22) 0 [0,11] d22 b12
  have b13 : a 8 ≠ 0 := exclude [2] (edge r28) (a 8) (a 9) 0 t2 c28 (by decide +kernel)
  have t13 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b13
  have b14 : a 10 ≠ 0 := exclude [1] (fun u v => edge r29 v u) (a 10) (a 8) 0 t13 c29 (by decide +kernel)
  have t14 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b14
  have b15 : a 24 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 24) (a 8) 0 t13 c31 (by decide +kernel)
  have t15 : a 24 ∈ [9] := remove (a 24) 0 [0,9] d24 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_187
