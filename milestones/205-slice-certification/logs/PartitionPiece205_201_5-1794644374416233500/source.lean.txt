import PartitionData205_201
namespace PartitionCover205_201
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6,14,15])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,14,16,20])
    (d27 : a 27 ∈ [0,11])
    (d31 : a 31 ∈ [0,2,3,11])
    (d28 : a 28 ∈ [0,4,10,11])
    (d30 : a 30 ∈ [0,2,19,23])
    (d1 : a 1 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,2])
    (d5 : a 5 ∈ [0,2,4,5])
    (d7 : a 7 ∈ [0,4])
    (d14 : a 14 ∈ [0,1,12,13])
    (d16 : a 16 ∈ [0,8,12,16])
    (d17 : a 17 ∈ [0,6])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 24 ∈ [0,6] ∧ a 26 ∈ [0,20] ∧ a 31 ∈ [0,11] ∧ a 28 ∈ [0,4] ∧ a 30 ∈ [0,23] ∧ a 1 ∈ [0,1] ∧ a 5 ∈ [0,2] ∧ a 14 ∈ [0,13] ∧ a 16 ∈ [0,12,16] := by
  have b0 : a 24 ≠ 14 := exclude [0,3] (edge r68) (a 24) (a 25) 14 d25 c68 (by decide +kernel)
  have t0 : a 24 ∈ [0,6,15] := remove (a 24) 14 [0,6,14,15] d24 b0
  have b1 : a 24 ≠ 15 := exclude [0,3] (edge r68) (a 24) (a 25) 15 d25 c68 (by decide +kernel)
  have t1 : a 24 ∈ [0,6] := remove (a 24) 15 [0,6,15] t0 b1
  have b2 : a 26 ≠ 14 := exclude [0,11] (edge r73) (a 26) (a 27) 14 d27 c73 (by decide +kernel)
  have t2 : a 26 ∈ [0,16,20] := remove (a 26) 14 [0,14,16,20] d26 b2
  have b3 : a 26 ≠ 16 := exclude [0,11] (edge r73) (a 26) (a 27) 16 d27 c73 (by decide +kernel)
  have t3 : a 26 ∈ [0,20] := remove (a 26) 16 [0,16,20] t2 b3
  have b4 : a 31 ≠ 2 := exclude [0,11] (fun u v => edge r75 v u) (a 31) (a 27) 2 d27 c75 (by decide +kernel)
  have t4 : a 31 ∈ [0,3,11] := remove (a 31) 2 [0,2,3,11] d31 b4
  have b5 : a 31 ≠ 3 := exclude [0,11] (fun u v => edge r75 v u) (a 31) (a 27) 3 d27 c75 (by decide +kernel)
  have t5 : a 31 ∈ [0,11] := remove (a 31) 3 [0,3,11] t4 b5
  have b6 : a 28 ≠ 10 := exclude [0,2,19,23] (edge r77) (a 28) (a 30) 10 d30 c77 (by decide +kernel)
  have t6 : a 28 ∈ [0,4,11] := remove (a 28) 10 [0,4,10,11] d28 b6
  have b7 : a 28 ≠ 11 := exclude [0,2,19,23] (edge r77) (a 28) (a 30) 11 d30 c77 (by decide +kernel)
  have t7 : a 28 ∈ [0,4] := remove (a 28) 11 [0,4,11] t6 b7
  have b8 : a 30 ≠ 2 := exclude [0,4] (fun u v => edge r77 v u) (a 30) (a 28) 2 t7 c77 (by decide +kernel)
  have t8 : a 30 ∈ [0,19,23] := remove (a 30) 2 [0,2,19,23] d30 b8
  have b9 : a 30 ≠ 19 := exclude [0,4] (fun u v => edge r77 v u) (a 30) (a 28) 19 t7 c77 (by decide +kernel)
  have t9 : a 30 ∈ [0,23] := remove (a 30) 19 [0,19,23] t8 b9
  have b10 : a 1 ≠ 2 := exclude [0,2] (edge r7) (a 1) (a 9) 2 d9 c7 (by decide +kernel)
  have t10 : a 1 ∈ [0,1] := remove (a 1) 2 [0,1,2] d1 b10
  have b11 : a 5 ≠ 4 := exclude [0,4] (edge r20) (a 5) (a 7) 4 d7 c20 (by decide +kernel)
  have t11 : a 5 ∈ [0,2,5] := remove (a 5) 4 [0,2,4,5] d5 b11
  have b12 : a 5 ≠ 5 := exclude [0,4] (edge r20) (a 5) (a 7) 5 d7 c20 (by decide +kernel)
  have t12 : a 5 ∈ [0,2] := remove (a 5) 5 [0,2,5] t11 b12
  have b13 : a 14 ≠ 1 := exclude [0,23] (edge r46) (a 14) (a 30) 1 t9 c46 (by decide +kernel)
  have t13 : a 14 ∈ [0,12,13] := remove (a 14) 1 [0,1,12,13] d14 b13
  have b14 : a 14 ≠ 12 := exclude [0,23] (edge r46) (a 14) (a 30) 12 t9 c46 (by decide +kernel)
  have t14 : a 14 ∈ [0,13] := remove (a 14) 12 [0,12,13] t13 b14
  have b15 : a 16 ≠ 8 := exclude [0,6] (edge r48) (a 16) (a 17) 8 d17 c48 (by decide +kernel)
  have t15 : a 16 ∈ [0,12,16] := remove (a 16) 8 [0,8,12,16] d16 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk21 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,12,16])
    (d17 : a 17 ∈ [0,6])
    (d20 : a 20 ∈ [0,6,8,12])
    (d21 : a 21 ∈ [0,6])
    (d4 : a 4 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,2])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 16 ∈ [0,12] ∧ a 20 ∈ [0,12] ∧ a 4 ∈ [0,1] := by
  have b0 : a 16 ≠ 16 := exclude [0,6] (edge r48) (a 16) (a 17) 16 d17 c48 (by decide +kernel)
  have t0 : a 16 ∈ [0,12] := remove (a 16) 16 [0,12,16] d16 b0
  have b1 : a 20 ≠ 6 := exclude [0,6] (edge r60) (a 20) (a 21) 6 d21 c60 (by decide +kernel)
  have t1 : a 20 ∈ [0,8,12] := remove (a 20) 6 [0,6,8,12] d20 b1
  have b2 : a 20 ≠ 8 := exclude [0,6] (edge r60) (a 20) (a 21) 8 d21 c60 (by decide +kernel)
  have t2 : a 20 ∈ [0,12] := remove (a 20) 8 [0,8,12] t1 b2
  have b3 : a 4 ≠ 2 := exclude [0,2] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,3] := remove (a 4) 2 [0,1,2,3] d4 b3
  have b4 : a 4 ≠ 3 := exclude [0,2] (edge r16) (a 4) (a 5) 3 d5 c16 (by decide +kernel)
  have t4 : a 4 ∈ [0,1] := remove (a 4) 3 [0,1,3] t3 b4
  exact And.intro t0 (And.intro t2 (t4))

theorem chunk22 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,2])
    (d17 : a 17 ∈ [0,6])
    (d2 : a 2 ∈ [0,8])
    (d6 : a 6 ∈ [0,5])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,8])
    (d7 : a 7 ∈ [0,4])
    (d19 : a 19 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,8])
    (d20 : a 20 ∈ [0,12])
    (d14 : a 14 ∈ [0,13])
    (d22 : a 22 ∈ [0,11])
    (d15 : a 15 ∈ [0,8])
    (d8 : a 8 ∈ [0,8])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 3 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 7 ∈ [0] ∧ a 19 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 3 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 2 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b0
  have b1 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b1
  have b2 : a 17 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 6 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 6 [0,6] d17 b2
  have b3 : a 2 ≠ 8 := exclude [0] (edge r9) (a 2) (a 3) 8 t0 c9 (by decide +kernel)
  have t3 : a 2 ∈ [0] := remove (a 2) 8 [0,8] d2 b3
  have b4 : a 6 ≠ 5 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 5 t3 c10 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 5 [0,5] d6 b4
  have b5 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 t3 c11 (by decide +kernel)
  have t5 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b5
  have b6 : a 18 ≠ 8 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 8 t3 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0] := remove (a 18) 8 [0,8] d18 b6
  have b7 : a 7 ≠ 4 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 4 t0 c13 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 4 [0,4] d7 b7
  have b8 : a 19 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 1 t0 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b8
  have b9 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t4 c17 (by decide +kernel)
  have t9 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b9
  have b10 : a 12 ≠ 8 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 8 t9 c18 (by decide +kernel)
  have t10 : a 12 ∈ [0] := remove (a 12) 8 [0,8] d12 b10
  have b11 : a 20 ≠ 12 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 12 t9 c19 (by decide +kernel)
  have t11 : a 20 ∈ [0] := remove (a 20) 12 [0,12] d20 b11
  have b12 : a 14 ≠ 13 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 13 t4 c24 (by decide +kernel)
  have t12 : a 14 ∈ [0] := remove (a 14) 13 [0,13] d14 b12
  have b13 : a 22 ≠ 11 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 11 t4 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0] := remove (a 22) 11 [0,11] d22 b13
  have b14 : a 15 ≠ 8 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 8 t7 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0] := remove (a 15) 8 [0,8] d15 b14
  have b15 : a 8 ≠ 8 := exclude [0] (edge r28) (a 8) (a 9) 8 t1 c28 (by decide +kernel)
  have t15 : a 8 ∈ [0] := remove (a 8) 8 [0,8] d8 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk23 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,6])
    (d8 : a 8 ∈ [0])
    (d13 : a 13 ∈ [0,4])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,20])
    (d10 : a 10 ∈ [0])
    (d11 : a 11 ∈ [0,16])
    (d15 : a 15 ∈ [0])
    (d27 : a 27 ∈ [0,11])
    (d28 : a 28 ∈ [0,4])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,8])
    (d30 : a 30 ∈ [0,23])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,11])
    (d16 : a 16 ∈ [0,12])
    (d17 : a 17 ∈ [0])
    (d21 : a 21 ∈ [0,6])
    (d23 : a 23 ∈ [0,1])
    (d5 : a 5 ∈ [0,2])
    (d4 : a 4 ∈ [0])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 24 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 11 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 21 ∈ [0] ∧ a 23 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0] := remove (a 24) 6 [0,6] d24 b0
  have b1 : a 13 ≠ 4 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [0] := remove (a 13) 4 [0,4] d13 b1
  have b2 : a 25 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 3 [0,3] d25 b2
  have b3 : a 26 ≠ 20 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 20 d10 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0] := remove (a 26) 20 [0,20] d26 b3
  have b4 : a 11 ≠ 16 := exclude [0] (edge r38) (a 11) (a 15) 16 d15 c38 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 16 [0,16] d11 b4
  have b5 : a 27 ≠ 11 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 11 t4 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0] := remove (a 27) 11 [0,11] d27 b5
  have b6 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0] := remove (a 28) 4 [0,4] d28 b6
  have b7 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 t1 c44 (by decide +kernel)
  have t7 : a 29 ∈ [0] := remove (a 29) 8 [0,8] d29 b7
  have b8 : a 30 ≠ 23 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 23 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0] := remove (a 30) 23 [0,23] d30 b8
  have b9 : a 31 ≠ 11 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 11 d15 c47 (by decide +kernel)
  have t9 : a 31 ∈ [0] := remove (a 31) 11 [0,11] d31 b9
  have b10 : a 16 ≠ 12 := exclude [0] (edge r48) (a 16) (a 17) 12 d17 c48 (by decide +kernel)
  have t10 : a 16 ∈ [0] := remove (a 16) 12 [0,12] d16 b10
  have b11 : a 21 ≠ 6 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 6 d17 c53 (by decide +kernel)
  have t11 : a 21 ∈ [0] := remove (a 21) 6 [0,6] d21 b11
  have b12 : a 23 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 1 t11 c63 (by decide +kernel)
  have t12 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b12
  have b13 : a 5 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 2 d4 c16 (by decide +kernel)
  have t13 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

#print axioms chunk20
#print axioms chunk21
#print axioms chunk22
#print axioms chunk23
end PartitionCover205_201
