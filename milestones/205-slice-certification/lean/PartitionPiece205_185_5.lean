import PartitionData205_185
namespace PartitionCover205_185
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,2,3,4,5])
    (d5 : a 5 ∈ [0,12])
    (c16 : edge r16 (a 4) (a 5)=true)
    : a 4 ∈ [0,3] := by
  have b0 : a 4 ≠ 2 := exclude [0,12] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t0 : a 4 ∈ [0,3,4,5] := remove (a 4) 2 [0,2,3,4,5] d4 b0
  have b1 : a 4 ≠ 4 := exclude [0,12] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t1 : a 4 ∈ [0,3,5] := remove (a 4) 4 [0,3,4,5] t0 b1
  have b2 : a 4 ≠ 5 := exclude [0,12] (edge r16) (a 4) (a 5) 5 d5 c16 (by decide +kernel)
  have t2 : a 4 ∈ [0,3] := remove (a 4) 5 [0,3,5] t1 b2
  exact t2

theorem chunk21 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,6])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,4])
    (d2 : a 2 ∈ [0,6])
    (d18 : a 18 ∈ [0,3])
    (d7 : a 7 ∈ [0,10])
    (d11 : a 11 ∈ [0,18])
    (d19 : a 19 ∈ [0,6])
    (d6 : a 6 ∈ [0,9])
    (d14 : a 14 ∈ [0,4])
    (d22 : a 22 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,9])
    (d13 : a 13 ∈ [0,2])
    (d25 : a 25 ∈ [0,2])
    (d10 : a 10 ∈ [0,23])
    (d26 : a 26 ∈ [0,10])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 3 ∈ [0] ∧ a 9 ∈ [0] ∧ a 2 ∈ [0] ∧ a 18 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 6 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 10 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 3 ≠ 6 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 6 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 6 [0,6] d3 b0
  have b1 : a 9 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 4 [0,4] d9 b1
  have b2 : a 2 ≠ 6 := exclude [0] (edge r9) (a 2) (a 3) 6 t0 c9 (by decide +kernel)
  have t2 : a 2 ∈ [0] := remove (a 2) 6 [0,6] d2 b2
  have b3 : a 18 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 3 t2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [0] := remove (a 18) 3 [0,3] d18 b3
  have b4 : a 7 ≠ 10 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 10 t0 c13 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 10 [0,10] d7 b4
  have b5 : a 11 ≠ 18 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 18 t0 c14 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 18 [0,18] d11 b5
  have b6 : a 19 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 6 t0 c15 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 6 [0,6] d19 b6
  have b7 : a 6 ≠ 9 := exclude [0] (edge r23) (a 6) (a 7) 9 t4 c23 (by decide +kernel)
  have t7 : a 6 ∈ [0] := remove (a 6) 9 [0,9] d6 b7
  have b8 : a 14 ≠ 4 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 4 t7 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 4 [0,4] d14 b8
  have b9 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 t7 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b9
  have b10 : a 8 ≠ 2 := exclude [0] (edge r28) (a 8) (a 9) 2 t1 c28 (by decide +kernel)
  have t10 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b10
  have b11 : a 12 ≠ 9 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 9 t10 c30 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 9 [0,9] d12 b11
  have b12 : a 13 ≠ 2 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 2 t1 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b12
  have b13 : a 25 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 2 t1 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b13
  have b14 : a 10 ≠ 23 := exclude [0] (edge r36) (a 10) (a 14) 23 t8 c36 (by decide +kernel)
  have t14 : a 10 ∈ [0] := remove (a 10) 23 [0,23] d10 b14
  have b15 : a 26 ≠ 10 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 10 t14 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 10 [0,10] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk22 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,2])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,9])
    (d28 : a 28 ∈ [0,14])
    (d12 : a 12 ∈ [0])
    (d30 : a 30 ∈ [0,4])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,6])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d20 : a 20 ∈ [0,2])
    (d24 : a 24 ∈ [0,4])
    (d17 : a 17 ∈ [0,2])
    (d25 : a 25 ∈ [0])
    (d21 : a 21 ∈ [0,4])
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d29 : a 29 ∈ [0,4])
    (d4 : a 4 ∈ [0,3])
    (d5 : a 5 ∈ [0,12])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 15 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 20 ∈ [0] ∧ a 24 ∈ [0] ∧ a 17 ∈ [0] ∧ a 21 ∈ [0] ∧ a 23 ∈ [0] ∧ a 29 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b0
  have b1 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 9 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0] := remove (a 27) 9 [0,9] d27 b1
  have b2 : a 28 ≠ 14 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 14 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0] := remove (a 28) 14 [0,14] d28 b2
  have b3 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 4 [0,4] d30 b3
  have b4 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 t0 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0] := remove (a 31) 6 [0,6] d31 b4
  have b5 : a 16 ≠ 1 := exclude [0] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t5 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b5
  have b6 : a 20 ≠ 2 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 2 t5 c50 (by decide +kernel)
  have t6 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b6
  have b7 : a 24 ≠ 4 := exclude [0] (fun u v => edge r51 v u) (a 24) (a 16) 4 t5 c51 (by decide +kernel)
  have t7 : a 24 ∈ [0] := remove (a 24) 4 [0,4] d24 b7
  have b8 : a 17 ≠ 2 := exclude [0] (edge r54) (a 17) (a 25) 2 d25 c54 (by decide +kernel)
  have t8 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b8
  have b9 : a 21 ≠ 4 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 4 t6 c60 (by decide +kernel)
  have t9 : a 21 ∈ [0] := remove (a 21) 4 [0,4] d21 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 1 d22 c65 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b10
  have b11 : a 29 ≠ 4 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 4 d25 c72 (by decide +kernel)
  have t11 : a 29 ∈ [0] := remove (a 29) 4 [0,4] d29 b11
  have b12 : a 4 ≠ 3 := exclude [0] (edge r18) (a 4) (a 12) 3 d12 c18 (by decide +kernel)
  have t12 : a 4 ∈ [0] := remove (a 4) 3 [0,3] d4 b12
  have b13 : a 5 ≠ 12 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 12 t12 c16 (by decide +kernel)
  have t13 : a 5 ∈ [0] := remove (a 5) 12 [0,12] d5 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

theorem chunk23 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,6])
    (d1 : a 1 ∈ [1])
    (d9 : a 9 ∈ [0,4])
    (d2 : a 2 ∈ [0,6])
    (d18 : a 18 ∈ [0,3])
    (d7 : a 7 ∈ [0,10])
    (d11 : a 11 ∈ [0,18])
    (d19 : a 19 ∈ [0,6])
    (d6 : a 6 ∈ [0,9])
    (d14 : a 14 ∈ [0,4])
    (d22 : a 22 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,9])
    (d13 : a 13 ∈ [0,2])
    (d25 : a 25 ∈ [0,2])
    (d10 : a 10 ∈ [0,23])
    (d26 : a 26 ∈ [0,10])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 3 ∈ [6] ∧ a 9 ∈ [4] ∧ a 2 ∈ [6] ∧ a 18 ∈ [3] ∧ a 7 ∈ [10] ∧ a 11 ∈ [18] ∧ a 19 ∈ [6] ∧ a 6 ∈ [9] ∧ a 14 ∈ [4] ∧ a 22 ∈ [1] ∧ a 8 ∈ [2] ∧ a 12 ∈ [9] ∧ a 13 ∈ [2] ∧ a 25 ∈ [2] ∧ a 10 ∈ [23] ∧ a 26 ∈ [10] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [6] := remove (a 3) 0 [0,6] d3 b0
  have b1 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [4] := remove (a 9) 0 [0,4] d9 b1
  have b2 : a 2 ≠ 0 := exclude [6] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t2 : a 2 ∈ [6] := remove (a 2) 0 [0,6] d2 b2
  have b3 : a 18 ≠ 0 := exclude [6] (fun u v => edge r12 v u) (a 18) (a 2) 0 t2 c12 (by decide +kernel)
  have t3 : a 18 ∈ [3] := remove (a 18) 0 [0,3] d18 b3
  have b4 : a 7 ≠ 0 := exclude [6] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t4 : a 7 ∈ [10] := remove (a 7) 0 [0,10] d7 b4
  have b5 : a 11 ≠ 0 := exclude [6] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t5 : a 11 ∈ [18] := remove (a 11) 0 [0,18] d11 b5
  have b6 : a 19 ≠ 0 := exclude [6] (fun u v => edge r15 v u) (a 19) (a 3) 0 t0 c15 (by decide +kernel)
  have t6 : a 19 ∈ [6] := remove (a 19) 0 [0,6] d19 b6
  have b7 : a 6 ≠ 0 := exclude [10] (edge r23) (a 6) (a 7) 0 t4 c23 (by decide +kernel)
  have t7 : a 6 ∈ [9] := remove (a 6) 0 [0,9] d6 b7
  have b8 : a 14 ≠ 0 := exclude [9] (fun u v => edge r24 v u) (a 14) (a 6) 0 t7 c24 (by decide +kernel)
  have t8 : a 14 ∈ [4] := remove (a 14) 0 [0,4] d14 b8
  have b9 : a 22 ≠ 0 := exclude [9] (fun u v => edge r25 v u) (a 22) (a 6) 0 t7 c25 (by decide +kernel)
  have t9 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b9
  have b10 : a 8 ≠ 0 := exclude [4] (edge r28) (a 8) (a 9) 0 t1 c28 (by decide +kernel)
  have t10 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b10
  have b11 : a 12 ≠ 0 := exclude [2] (fun u v => edge r30 v u) (a 12) (a 8) 0 t10 c30 (by decide +kernel)
  have t11 : a 12 ∈ [9] := remove (a 12) 0 [0,9] d12 b11
  have b12 : a 13 ≠ 0 := exclude [4] (fun u v => edge r33 v u) (a 13) (a 9) 0 t1 c33 (by decide +kernel)
  have t12 : a 13 ∈ [2] := remove (a 13) 0 [0,2] d13 b12
  have b13 : a 25 ≠ 0 := exclude [4] (fun u v => edge r34 v u) (a 25) (a 9) 0 t1 c34 (by decide +kernel)
  have t13 : a 25 ∈ [2] := remove (a 25) 0 [0,2] d25 b13
  have b14 : a 10 ≠ 0 := exclude [4] (edge r36) (a 10) (a 14) 0 t8 c36 (by decide +kernel)
  have t14 : a 10 ∈ [23] := remove (a 10) 0 [0,23] d10 b14
  have b15 : a 26 ≠ 0 := exclude [23] (fun u v => edge r37 v u) (a 26) (a 10) 0 t14 c37 (by decide +kernel)
  have t15 : a 26 ∈ [10] := remove (a 26) 0 [0,10] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_185
