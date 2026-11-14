import PartitionData205_200
namespace PartitionCover205_200
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,3,5])
    (d30 : a 30 ∈ [0,19])
    (d1 : a 1 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,4])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,1,4,5,6,7,8,9])
    (d12 : a 12 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d8 : a 8 ∈ [0,3,8,11])
    (d10 : a 10 ∈ [0,1,2])
    (d26 : a 26 ∈ [0,19])
    (d14 : a 14 ∈ [0,1,12,13])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 28 ∈ [0,3] ∧ a 1 ∈ [0,1] ∧ a 5 ∈ [0,4] ∧ a 4 ∈ [0,4,7,8] ∧ a 8 ∈ [0,8] ∧ a 10 ∈ [0,1] ∧ a 14 ∈ [0,12] := by
  have b0 : a 28 ≠ 2 := exclude [0,19] (edge r77) (a 28) (a 30) 2 d30 c77 (by decide +kernel)
  have t0 : a 28 ∈ [0,3,5] := remove (a 28) 2 [0,2,3,5] d28 b0
  have b1 : a 28 ≠ 5 := exclude [0,19] (edge r77) (a 28) (a 30) 5 d30 c77 (by decide +kernel)
  have t1 : a 28 ∈ [0,3] := remove (a 28) 5 [0,3,5] t0 b1
  have b2 : a 1 ≠ 2 := exclude [0,4] (edge r7) (a 1) (a 9) 2 d9 c7 (by decide +kernel)
  have t2 : a 1 ∈ [0,1] := remove (a 1) 2 [0,1,2] d1 b2
  have b3 : a 5 ≠ 1 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t3 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b3
  have b4 : a 5 ≠ 5 := exclude [0,1,4,5,6,7,8,9] (fun u v => edge r16 v u) (a 5) (a 4) 5 d4 c16 (by decide +kernel)
  have t4 : a 5 ∈ [0,2,3,4] := remove (a 5) 5 [0,2,3,4,5] t3 b4
  have b5 : a 4 ≠ 1 := exclude [0,1] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t5 : a 4 ∈ [0,4,5,6,7,8,9] := remove (a 4) 1 [0,1,4,5,6,7,8,9] d4 b5
  have b6 : a 4 ≠ 5 := exclude [0,1] (edge r18) (a 4) (a 12) 5 d12 c18 (by decide +kernel)
  have t6 : a 4 ∈ [0,4,6,7,8,9] := remove (a 4) 5 [0,4,5,6,7,8,9] t5 b6
  have b7 : a 4 ≠ 6 := exclude [0,1] (edge r18) (a 4) (a 12) 6 d12 c18 (by decide +kernel)
  have t7 : a 4 ∈ [0,4,7,8,9] := remove (a 4) 6 [0,4,6,7,8,9] t6 b7
  have b8 : a 4 ≠ 9 := exclude [0,1] (edge r18) (a 4) (a 12) 9 d12 c18 (by decide +kernel)
  have t8 : a 4 ∈ [0,4,7,8] := remove (a 4) 9 [0,4,7,8,9] t7 b8
  have b9 : a 5 ≠ 2 := exclude [0,1] (edge r21) (a 5) (a 13) 2 d13 c21 (by decide +kernel)
  have t9 : a 5 ∈ [0,3,4] := remove (a 5) 2 [0,2,3,4] t4 b9
  have b10 : a 5 ≠ 3 := exclude [0,1] (edge r21) (a 5) (a 13) 3 d13 c21 (by decide +kernel)
  have t10 : a 5 ∈ [0,4] := remove (a 5) 3 [0,3,4] t9 b10
  have b11 : a 8 ≠ 3 := exclude [0,4] (edge r28) (a 8) (a 9) 3 d9 c28 (by decide +kernel)
  have t11 : a 8 ∈ [0,8,11] := remove (a 8) 3 [0,3,8,11] d8 b11
  have b12 : a 8 ≠ 11 := exclude [0,4] (edge r28) (a 8) (a 9) 11 d9 c28 (by decide +kernel)
  have t12 : a 8 ∈ [0,8] := remove (a 8) 11 [0,8,11] t11 b12
  have b13 : a 10 ≠ 2 := exclude [0,19] (edge r37) (a 10) (a 26) 2 d26 c37 (by decide +kernel)
  have t13 : a 10 ∈ [0,1] := remove (a 10) 2 [0,1,2] d10 b13
  have b14 : a 14 ≠ 1 := exclude [0,19] (edge r46) (a 14) (a 30) 1 d30 c46 (by decide +kernel)
  have t14 : a 14 ∈ [0,12,13] := remove (a 14) 1 [0,1,12,13] d14 b14
  have b15 : a 14 ≠ 13 := exclude [0,19] (edge r46) (a 14) (a 30) 13 d30 c46 (by decide +kernel)
  have t15 : a 14 ∈ [0,12] := remove (a 14) 13 [0,12,13] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t10 (And.intro t8 (And.intro t12 (And.intro t13 (t15))))))

theorem chunk17 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,2])
    (d20 : a 20 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,2])
    (d4 : a 4 ∈ [0,4,7,8])
    (d5 : a 5 ∈ [0,4])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 16 ∈ [0,2] ∧ a 20 ∈ [0,2] ∧ a 4 ∈ [0,8] := by
  have b0 : a 16 ≠ 1 := exclude [0,2] (edge r48) (a 16) (a 17) 1 d17 c48 (by decide +kernel)
  have t0 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b0
  have b1 : a 16 ≠ 3 := exclude [0,2] (edge r48) (a 16) (a 17) 3 d17 c48 (by decide +kernel)
  have t1 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t0 b1
  have b2 : a 20 ≠ 1 := exclude [0,2] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t2 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b2
  have b3 : a 20 ≠ 3 := exclude [0,2] (edge r60) (a 20) (a 21) 3 d21 c60 (by decide +kernel)
  have t3 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t2 b3
  have b4 : a 4 ≠ 4 := exclude [0,4] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t4 : a 4 ∈ [0,7,8] := remove (a 4) 4 [0,4,7,8] d4 b4
  have b5 : a 4 ≠ 7 := exclude [0,4] (edge r16) (a 4) (a 5) 7 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0,8] := remove (a 4) 7 [0,7,8] t4 b5
  exact And.intro t1 (And.intro t3 (t5))

theorem chunk18 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,4])
    (d9 : a 9 ∈ [0,4])
    (d17 : a 17 ∈ [0,2])
    (d2 : a 2 ∈ [0,4])
    (d6 : a 6 ∈ [0,4])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,4])
    (d7 : a 7 ∈ [0,2])
    (d4 : a 4 ∈ [0,8])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d21 : a 21 ∈ [0,2])
    (d14 : a 14 ∈ [0,12])
    (d22 : a 22 ∈ [0,1])
    (d15 : a 15 ∈ [0,6])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] := by
  have b0 : a 3 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 2 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b0
  have b1 : a 5 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 4 [0,4] d5 b1
  have b2 : a 9 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 4 [0,4] d9 b2
  have b3 : a 17 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 2 d1 c8 (by decide +kernel)
  have t3 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b3
  have b4 : a 2 ≠ 4 := exclude [0] (edge r9) (a 2) (a 3) 4 t0 c9 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 4 [0,4] d2 b4
  have b5 : a 6 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 4 t4 c10 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b5
  have b6 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 t4 c11 (by decide +kernel)
  have t6 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b6
  have b7 : a 18 ≠ 4 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 4 t4 c12 (by decide +kernel)
  have t7 : a 18 ∈ [0] := remove (a 18) 4 [0,4] d18 b7
  have b8 : a 7 ≠ 2 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 2 t0 c13 (by decide +kernel)
  have t8 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b8
  have b9 : a 4 ≠ 8 := exclude [0] (edge r16) (a 4) (a 5) 8 t1 c16 (by decide +kernel)
  have t9 : a 4 ∈ [0] := remove (a 4) 8 [0,8] d4 b9
  have b10 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t9 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b10
  have b11 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 t9 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b11
  have b12 : a 21 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 2 t1 c22 (by decide +kernel)
  have t12 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b12
  have b13 : a 14 ≠ 12 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 12 t5 c24 (by decide +kernel)
  have t13 : a 14 ∈ [0] := remove (a 14) 12 [0,12] d14 b13
  have b14 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 t5 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b14
  have b15 : a 15 ≠ 6 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 6 t8 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0] := remove (a 15) 6 [0,6] d15 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk19 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,8])
    (d9 : a 9 ∈ [0])
    (d24 : a 24 ∈ [0,4])
    (d26 : a 26 ∈ [0,19])
    (d10 : a 10 ∈ [0])
    (d11 : a 11 ∈ [0,12])
    (d15 : a 15 ∈ [0])
    (d27 : a 27 ∈ [0,9])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0,19])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,9])
    (d16 : a 16 ∈ [0,2])
    (d17 : a 17 ∈ [0])
    (d23 : a 23 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d28 : a 28 ∈ [0,3])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    : a 8 ∈ [0] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0] ∧ a 11 ∈ [0] ∧ a 27 ∈ [0] ∧ a 13 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 23 ∈ [0] ∧ a 25 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 8 ≠ 8 := exclude [0] (edge r28) (a 8) (a 9) 8 d9 c28 (by decide +kernel)
  have t0 : a 8 ∈ [0] := remove (a 8) 8 [0,8] d8 b0
  have b1 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 t0 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0] := remove (a 24) 4 [0,4] d24 b1
  have b2 : a 26 ≠ 19 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 19 d10 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0] := remove (a 26) 19 [0,19] d26 b2
  have b3 : a 11 ≠ 12 := exclude [0] (edge r38) (a 11) (a 15) 12 d15 c38 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 12 [0,12] d11 b3
  have b4 : a 27 ≠ 9 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 9 t3 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0] := remove (a 27) 9 [0,9] d27 b4
  have b5 : a 13 ≠ 1 := exclude [0] (edge r43) (a 13) (a 15) 1 d15 c43 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b5
  have b6 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 t5 c44 (by decide +kernel)
  have t6 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b6
  have b7 : a 30 ≠ 19 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 19 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0] := remove (a 30) 19 [0,19] d30 b7
  have b8 : a 31 ≠ 9 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 9 d15 c47 (by decide +kernel)
  have t8 : a 31 ∈ [0] := remove (a 31) 9 [0,9] d31 b8
  have b9 : a 16 ≠ 2 := exclude [0] (edge r48) (a 16) (a 17) 2 d17 c48 (by decide +kernel)
  have t9 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 1 d21 c63 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b10
  have b11 : a 25 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 1 t1 c68 (by decide +kernel)
  have t11 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b11
  have b12 : a 28 ≠ 3 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 3 t1 c70 (by decide +kernel)
  have t12 : a 28 ∈ [0] := remove (a 28) 3 [0,3] d28 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))

#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_200
