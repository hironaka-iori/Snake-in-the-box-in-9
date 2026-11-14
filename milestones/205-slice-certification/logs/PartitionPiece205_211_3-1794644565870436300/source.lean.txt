import PartitionData205_211
namespace PartitionCover205_211
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,6])
    (d4 : a 4 ∈ [0,3])
    (d6 : a 6 ∈ [0,6])
    (d7 : a 7 ∈ [0,1])
    (d13 : a 13 ∈ [0,3])
    (d21 : a 21 ∈ [0,1])
    (d14 : a 14 ∈ [0,3])
    (d22 : a 22 ∈ [0,6])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,3])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,6])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 5 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b0
  have b1 : a 9 ≠ 6 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 6 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 6 [0,6] d9 b1
  have b2 : a 4 ≠ 3 := exclude [0] (edge r16) (a 4) (a 5) 3 t0 c16 (by decide +kernel)
  have t2 : a 4 ∈ [0] := remove (a 4) 3 [0,3] d4 b2
  have b3 : a 6 ≠ 6 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 6 t2 c17 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 6 [0,6] d6 b3
  have b4 : a 7 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 1 t0 c20 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b4
  have b5 : a 13 ≠ 3 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 3 t0 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 3 [0,3] d13 b5
  have b6 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 t0 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b6
  have b7 : a 14 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 3 t3 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 3 [0,3] d14 b7
  have b8 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 t3 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 6 [0,6] d22 b8
  have b9 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 t4 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 t4 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b10
  have b11 : a 8 ≠ 3 := exclude [0] (edge r28) (a 8) (a 9) 3 t1 c28 (by decide +kernel)
  have t11 : a 8 ∈ [0] := remove (a 8) 3 [0,3] d8 b11
  have b12 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 t11 c29 (by decide +kernel)
  have t12 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b12
  have b13 : a 11 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 1 t1 c32 (by decide +kernel)
  have t13 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b13
  have b14 : a 25 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 3 t1 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0] := remove (a 25) 3 [0,3] d25 b14
  have b15 : a 26 ≠ 6 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 6 t12 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 6 [0,6] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk13 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,6])
    (d13 : a 13 ∈ [0])
    (d31 : a 31 ∈ [0,3])
    (d15 : a 15 ∈ [0])
    (d17 : a 17 ∈ [0,2])
    (d25 : a 25 ∈ [0])
    (d19 : a 19 ∈ [0,2])
    (d23 : a 23 ∈ [0])
    (d27 : a 27 ∈ [0,6])
    (d28 : a 28 ∈ [0,9])
    (d30 : a 30 ∈ [0,18])
    (d2 : a 2 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d18 : a 18 ∈ [0,2])
    (d16 : a 16 ∈ [0,2])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 29 ∈ [0] ∧ a 31 ∈ [0] ∧ a 17 ∈ [0] ∧ a 19 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 30 ∈ [0] ∧ a 2 ∈ [0] ∧ a 18 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0] := remove (a 29) 6 [0,6] d29 b0
  have b1 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0] := remove (a 31) 3 [0,3] d31 b1
  have b2 : a 17 ≠ 2 := exclude [0] (edge r54) (a 17) (a 25) 2 d25 c54 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b2
  have b3 : a 19 ≠ 2 := exclude [0] (edge r58) (a 19) (a 23) 2 d23 c58 (by decide +kernel)
  have t3 : a 19 ∈ [0] := remove (a 19) 2 [0,2] d19 b3
  have b4 : a 27 ≠ 6 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 6 t3 c59 (by decide +kernel)
  have t4 : a 27 ∈ [0] := remove (a 27) 6 [0,6] d27 b4
  have b5 : a 28 ≠ 9 := exclude [0] (edge r76) (a 28) (a 29) 9 t0 c76 (by decide +kernel)
  have t5 : a 28 ∈ [0] := remove (a 28) 9 [0,9] d28 b5
  have b6 : a 30 ≠ 18 := exclude [0] (fun u v => edge r77 v u) (a 30) (a 28) 18 t5 c77 (by decide +kernel)
  have t6 : a 30 ∈ [0] := remove (a 30) 18 [0,18] d30 b6
  have b7 : a 2 ≠ 1 := exclude [0] (edge r11) (a 2) (a 10) 1 d10 c11 (by decide +kernel)
  have t7 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b7
  have b8 : a 18 ≠ 2 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 2 t7 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b8
  have b9 : a 16 ≠ 2 := exclude [0] (edge r48) (a 16) (a 17) 2 t2 c48 (by decide +kernel)
  have t9 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))

theorem chunk14 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d9 : a 9 ∈ [0,6])
    (d4 : a 4 ∈ [0,3])
    (d6 : a 6 ∈ [0,6])
    (d7 : a 7 ∈ [0,1])
    (d13 : a 13 ∈ [0,3])
    (d21 : a 21 ∈ [0,1])
    (d14 : a 14 ∈ [0,3])
    (d22 : a 22 ∈ [0,6])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,3])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,6])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 5 ∈ [1] ∧ a 9 ∈ [6] ∧ a 4 ∈ [3] ∧ a 6 ∈ [6] ∧ a 7 ∈ [1] ∧ a 13 ∈ [3] ∧ a 21 ∈ [1] ∧ a 14 ∈ [3] ∧ a 22 ∈ [6] ∧ a 15 ∈ [1] ∧ a 23 ∈ [1] ∧ a 8 ∈ [3] ∧ a 10 ∈ [2] ∧ a 11 ∈ [1] ∧ a 25 ∈ [3] ∧ a 26 ∈ [6] := by
  have b0 : a 5 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 5) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b0
  have b1 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [6] := remove (a 9) 0 [0,6] d9 b1
  have b2 : a 4 ≠ 0 := exclude [1] (edge r16) (a 4) (a 5) 0 t0 c16 (by decide +kernel)
  have t2 : a 4 ∈ [3] := remove (a 4) 0 [0,3] d4 b2
  have b3 : a 6 ≠ 0 := exclude [3] (fun u v => edge r17 v u) (a 6) (a 4) 0 t2 c17 (by decide +kernel)
  have t3 : a 6 ∈ [6] := remove (a 6) 0 [0,6] d6 b3
  have b4 : a 7 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 7) (a 5) 0 t0 c20 (by decide +kernel)
  have t4 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b4
  have b5 : a 13 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 13) (a 5) 0 t0 c21 (by decide +kernel)
  have t5 : a 13 ∈ [3] := remove (a 13) 0 [0,3] d13 b5
  have b6 : a 21 ≠ 0 := exclude [1] (fun u v => edge r22 v u) (a 21) (a 5) 0 t0 c22 (by decide +kernel)
  have t6 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b6
  have b7 : a 14 ≠ 0 := exclude [6] (fun u v => edge r24 v u) (a 14) (a 6) 0 t3 c24 (by decide +kernel)
  have t7 : a 14 ∈ [3] := remove (a 14) 0 [0,3] d14 b7
  have b8 : a 22 ≠ 0 := exclude [6] (fun u v => edge r25 v u) (a 22) (a 6) 0 t3 c25 (by decide +kernel)
  have t8 : a 22 ∈ [6] := remove (a 22) 0 [0,6] d22 b8
  have b9 : a 15 ≠ 0 := exclude [1] (fun u v => edge r26 v u) (a 15) (a 7) 0 t4 c26 (by decide +kernel)
  have t9 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b9
  have b10 : a 23 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 23) (a 7) 0 t4 c27 (by decide +kernel)
  have t10 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b10
  have b11 : a 8 ≠ 0 := exclude [6] (edge r28) (a 8) (a 9) 0 t1 c28 (by decide +kernel)
  have t11 : a 8 ∈ [3] := remove (a 8) 0 [0,3] d8 b11
  have b12 : a 10 ≠ 0 := exclude [3] (fun u v => edge r29 v u) (a 10) (a 8) 0 t11 c29 (by decide +kernel)
  have t12 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b12
  have b13 : a 11 ≠ 0 := exclude [6] (fun u v => edge r32 v u) (a 11) (a 9) 0 t1 c32 (by decide +kernel)
  have t13 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b13
  have b14 : a 25 ≠ 0 := exclude [6] (fun u v => edge r34 v u) (a 25) (a 9) 0 t1 c34 (by decide +kernel)
  have t14 : a 25 ∈ [3] := remove (a 25) 0 [0,3] d25 b14
  have b15 : a 26 ≠ 0 := exclude [2] (fun u v => edge r37 v u) (a 26) (a 10) 0 t12 c37 (by decide +kernel)
  have t15 : a 26 ∈ [6] := remove (a 26) 0 [0,6] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,6])
    (d13 : a 13 ∈ [3])
    (d31 : a 31 ∈ [0,3])
    (d15 : a 15 ∈ [1])
    (d17 : a 17 ∈ [0,2])
    (d25 : a 25 ∈ [3])
    (d19 : a 19 ∈ [0,2])
    (d23 : a 23 ∈ [1])
    (d27 : a 27 ∈ [0,6])
    (d28 : a 28 ∈ [0,9])
    (d30 : a 30 ∈ [0,18])
    (d2 : a 2 ∈ [0,1])
    (d10 : a 10 ∈ [2])
    (d18 : a 18 ∈ [0,2])
    (d16 : a 16 ∈ [0,2])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 29 ∈ [6] ∧ a 31 ∈ [3] ∧ a 17 ∈ [2] ∧ a 19 ∈ [2] ∧ a 27 ∈ [6] ∧ a 28 ∈ [9] ∧ a 30 ∈ [18] ∧ a 2 ∈ [1] ∧ a 18 ∈ [2] ∧ a 16 ∈ [2] := by
  have b0 : a 29 ≠ 0 := exclude [3] (fun u v => edge r44 v u) (a 29) (a 13) 0 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [6] := remove (a 29) 0 [0,6] d29 b0
  have b1 : a 31 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 31) (a 15) 0 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [3] := remove (a 31) 0 [0,3] d31 b1
  have b2 : a 17 ≠ 0 := exclude [3] (edge r54) (a 17) (a 25) 0 d25 c54 (by decide +kernel)
  have t2 : a 17 ∈ [2] := remove (a 17) 0 [0,2] d17 b2
  have b3 : a 19 ≠ 0 := exclude [1] (edge r58) (a 19) (a 23) 0 d23 c58 (by decide +kernel)
  have t3 : a 19 ∈ [2] := remove (a 19) 0 [0,2] d19 b3
  have b4 : a 27 ≠ 0 := exclude [2] (fun u v => edge r59 v u) (a 27) (a 19) 0 t3 c59 (by decide +kernel)
  have t4 : a 27 ∈ [6] := remove (a 27) 0 [0,6] d27 b4
  have b5 : a 28 ≠ 0 := exclude [6] (edge r76) (a 28) (a 29) 0 t0 c76 (by decide +kernel)
  have t5 : a 28 ∈ [9] := remove (a 28) 0 [0,9] d28 b5
  have b6 : a 30 ≠ 0 := exclude [9] (fun u v => edge r77 v u) (a 30) (a 28) 0 t5 c77 (by decide +kernel)
  have t6 : a 30 ∈ [18] := remove (a 30) 0 [0,18] d30 b6
  have b7 : a 2 ≠ 0 := exclude [2] (edge r11) (a 2) (a 10) 0 d10 c11 (by decide +kernel)
  have t7 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b7
  have b8 : a 18 ≠ 0 := exclude [1] (fun u v => edge r12 v u) (a 18) (a 2) 0 t7 c12 (by decide +kernel)
  have t8 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b8
  have b9 : a 16 ≠ 0 := exclude [2] (edge r48) (a 16) (a 17) 0 t2 c48 (by decide +kernel)
  have t9 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_211
