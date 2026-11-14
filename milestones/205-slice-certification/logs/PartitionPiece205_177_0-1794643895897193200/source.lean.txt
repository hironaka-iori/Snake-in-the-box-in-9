import PartitionData205_177
namespace PartitionCover205_177
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1,2])
    (d2 : a 2 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1,2,3,4,5])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    : a 4 ∈ [0,4] ∧ a 8 ∈ [0,2] ∧ a 3 ∈ [0,2] ∧ a 10 ∈ [0,2] ∧ a 7 ∈ [0,1,4,5] ∧ a 5 ∈ [0,4] ∧ a 6 ∈ [0,2,3,4,5] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,3,4,5] := remove (a 4) 2 [0,2,3,4,5] t0 b1
  have b2 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,4,5] := remove (a 4) 3 [0,3,4,5] t1 b2
  have b3 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,4] := remove (a 4) 5 [0,4,5] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b4
  have b5 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t4 b5
  have b6 : a 3 ≠ 1 := exclude [0,1] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t6 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b6
  have b7 : a 10 ≠ 1 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t7 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b7
  have b8 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t8 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t7 b8
  have b9 : a 7 ≠ 2 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 2 t6 c13 (by decide +kernel)
  have t9 : a 7 ∈ [0,1,3,4,5] := remove (a 7) 2 [0,1,2,3,4,5] d7 b9
  have b10 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 7) (a 3) 3 t6 c13 (by decide +kernel)
  have t10 : a 7 ∈ [0,1,4,5] := remove (a 7) 3 [0,1,3,4,5] t9 b10
  have b11 : a 5 ≠ 1 := exclude [0,4] (fun u v => edge r16 v u) (a 5) (a 4) 1 t3 c16 (by decide +kernel)
  have t11 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b11
  have b12 : a 5 ≠ 2 := exclude [0,4] (fun u v => edge r16 v u) (a 5) (a 4) 2 t3 c16 (by decide +kernel)
  have t12 : a 5 ∈ [0,3,4,5] := remove (a 5) 2 [0,2,3,4,5] t11 b12
  have b13 : a 5 ≠ 3 := exclude [0,4] (fun u v => edge r16 v u) (a 5) (a 4) 3 t3 c16 (by decide +kernel)
  have t13 : a 5 ∈ [0,4,5] := remove (a 5) 3 [0,3,4,5] t12 b13
  have b14 : a 5 ≠ 5 := exclude [0,4] (fun u v => edge r16 v u) (a 5) (a 4) 5 t3 c16 (by decide +kernel)
  have t14 : a 5 ∈ [0,4] := remove (a 5) 5 [0,4,5] t13 b14
  have b15 : a 6 ≠ 1 := exclude [0,4] (fun u v => edge r17 v u) (a 6) (a 4) 1 t3 c17 (by decide +kernel)
  have t15 : a 6 ∈ [0,2,3,4,5] := remove (a 6) 1 [0,1,2,3,4,5] d6 b15
  exact And.intro t3 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t14 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,2,3,4,5])
    (d4 : a 4 ∈ [0,4])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,1,4,5])
    (d5 : a 5 ∈ [0,4])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1])
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 6 ∈ [0,4] ∧ a 20 ∈ [0,1,8,9] ∧ a 7 ∈ [0,5] ∧ a 21 ∈ [0,1,2,4] ∧ a 22 ∈ [0] := by
  have b0 : a 6 ≠ 2 := exclude [0,4] (fun u v => edge r17 v u) (a 6) (a 4) 2 d4 c17 (by decide +kernel)
  have t0 : a 6 ∈ [0,3,4,5] := remove (a 6) 2 [0,2,3,4,5] d6 b0
  have b1 : a 6 ≠ 3 := exclude [0,4] (fun u v => edge r17 v u) (a 6) (a 4) 3 d4 c17 (by decide +kernel)
  have t1 : a 6 ∈ [0,4,5] := remove (a 6) 3 [0,3,4,5] t0 b1
  have b2 : a 6 ≠ 5 := exclude [0,4] (fun u v => edge r17 v u) (a 6) (a 4) 5 d4 c17 (by decide +kernel)
  have t2 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t1 b2
  have b3 : a 20 ≠ 2 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 20) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d20 b3
  have b4 : a 20 ≠ 3 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 3 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 20) 3 [0,1,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 20 ≠ 4 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 20) 4 [0,1,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 20 ≠ 5 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0,1,6,7,8,9,10,11] := remove (a 20) 5 [0,1,5,6,7,8,9,10,11] t5 b6
  have b7 : a 20 ≠ 6 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 6 d4 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,7,8,9,10,11] := remove (a 20) 6 [0,1,6,7,8,9,10,11] t6 b7
  have b8 : a 20 ≠ 7 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 7 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0,1,8,9,10,11] := remove (a 20) 7 [0,1,7,8,9,10,11] t7 b8
  have b9 : a 20 ≠ 10 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 10 d4 c19 (by decide +kernel)
  have t9 : a 20 ∈ [0,1,8,9,11] := remove (a 20) 10 [0,1,8,9,10,11] t8 b9
  have b10 : a 20 ≠ 11 := exclude [0,4] (fun u v => edge r19 v u) (a 20) (a 4) 11 d4 c19 (by decide +kernel)
  have t10 : a 20 ∈ [0,1,8,9] := remove (a 20) 11 [0,1,8,9,11] t9 b10
  have b11 : a 7 ≠ 1 := exclude [0,4] (fun u v => edge r20 v u) (a 7) (a 5) 1 d5 c20 (by decide +kernel)
  have t11 : a 7 ∈ [0,4,5] := remove (a 7) 1 [0,1,4,5] d7 b11
  have b12 : a 7 ≠ 4 := exclude [0,4] (fun u v => edge r20 v u) (a 7) (a 5) 4 d5 c20 (by decide +kernel)
  have t12 : a 7 ∈ [0,5] := remove (a 7) 4 [0,4,5] t11 b12
  have b13 : a 21 ≠ 3 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,2,4,5] := remove (a 21) 3 [0,1,2,3,4,5] d21 b13
  have b14 : a 21 ≠ 5 := exclude [0,4] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,1,2,4] := remove (a 21) 5 [0,1,2,4,5] t13 b14
  have b15 : a 22 ≠ 1 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 1 t2 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b15
  exact And.intro t2 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

theorem chunk2 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,2,3,4,5,6,7,8])
    (d7 : a 7 ∈ [0,5])
    (d12 : a 12 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,2])
    (d9 : a 9 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2,3])
    (d27 : a 27 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1])
    (d28 : a 28 ∈ [0,1,2,3,4,5])
    (c27 : edge r27 (a 7) (a 23)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 23 ∈ [0,2] ∧ a 12 ∈ [0] ∧ a 11 ∈ [0] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,1] ∧ a 13 ∈ [0] ∧ a 28 ∈ [0,2,3,4,5] := by
  have b0 : a 23 ≠ 1 := exclude [0,5] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t0 : a 23 ∈ [0,2,3,4,5,6,7,8] := remove (a 23) 1 [0,1,2,3,4,5,6,7,8] d23 b0
  have b1 : a 23 ≠ 3 := exclude [0,5] (fun u v => edge r27 v u) (a 23) (a 7) 3 d7 c27 (by decide +kernel)
  have t1 : a 23 ∈ [0,2,4,5,6,7,8] := remove (a 23) 3 [0,2,3,4,5,6,7,8] t0 b1
  have b2 : a 23 ≠ 4 := exclude [0,5] (fun u v => edge r27 v u) (a 23) (a 7) 4 d7 c27 (by decide +kernel)
  have t2 : a 23 ∈ [0,2,5,6,7,8] := remove (a 23) 4 [0,2,4,5,6,7,8] t1 b2
  have b3 : a 23 ≠ 5 := exclude [0,5] (fun u v => edge r27 v u) (a 23) (a 7) 5 d7 c27 (by decide +kernel)
  have t3 : a 23 ∈ [0,2,6,7,8] := remove (a 23) 5 [0,2,5,6,7,8] t2 b3
  have b4 : a 23 ≠ 6 := exclude [0,5] (fun u v => edge r27 v u) (a 23) (a 7) 6 d7 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,2,7,8] := remove (a 23) 6 [0,2,6,7,8] t3 b4
  have b5 : a 23 ≠ 7 := exclude [0,5] (fun u v => edge r27 v u) (a 23) (a 7) 7 d7 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,2,8] := remove (a 23) 7 [0,2,7,8] t4 b5
  have b6 : a 23 ≠ 8 := exclude [0,5] (fun u v => edge r27 v u) (a 23) (a 7) 8 d7 c27 (by decide +kernel)
  have t6 : a 23 ∈ [0,2] := remove (a 23) 8 [0,2,8] t5 b6
  have b7 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r30 v u) (a 12) (a 8) 1 d8 c30 (by decide +kernel)
  have t7 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b7
  have b8 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 1 d9 c32 (by decide +kernel)
  have t8 : a 11 ∈ [0,2] := remove (a 11) 1 [0,1,2] d11 b8
  have b9 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 2 [0,2] t8 b9
  have b10 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 t9 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,3] := remove (a 15) 2 [0,1,2,3] d15 b10
  have b11 : a 15 ≠ 3 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 3 t9 c38 (by decide +kernel)
  have t11 : a 15 ∈ [0,1] := remove (a 15) 3 [0,1,3] t10 b11
  have b12 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 t9 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,3] := remove (a 27) 2 [0,1,2,3] d27 b12
  have b13 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 t9 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0,1] := remove (a 27) 3 [0,1,3] t12 b13
  have b14 : a 13 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 1 t7 c40 (by decide +kernel)
  have t14 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b14
  have b15 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t7 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,3,4,5] := remove (a 28) 1 [0,1,2,3,4,5] d28 b15
  exact And.intro t6 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))))

theorem chunk3 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,3,4,5])
    (d12 : a 12 ∈ [0])
    (d19 : a 19 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,4])
    (d20 : a 20 ∈ [0,1,8,9])
    (d22 : a 22 ∈ [0])
    (d23 : a 23 ∈ [0,2])
    (d29 : a 29 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 28 ∈ [0,3] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0] ∧ a 20 ∈ [0,8] ∧ a 29 ∈ [0,1] ∧ a 30 ∈ [0,2] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0,2,3] := by
  have b0 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,3,4,5] := remove (a 28) 2 [0,2,3,4,5] d28 b0
  have b1 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,3,5] := remove (a 28) 4 [0,3,4,5] t0 b1
  have b2 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,3] := remove (a 28) 5 [0,3,5] t1 b2
  have b3 : a 19 ≠ 1 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t3 : a 19 ∈ [0,2] := remove (a 19) 1 [0,1,2] d19 b3
  have b4 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r52 v u) (a 19) (a 17) 2 d17 c52 (by decide +kernel)
  have t4 : a 19 ∈ [0] := remove (a 19) 2 [0,2] t3 b4
  have b5 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 2 d17 c53 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,4] := remove (a 21) 2 [0,1,2,4] d21 b5
  have b6 : a 21 ≠ 4 := exclude [0,1] (fun u v => edge r53 v u) (a 21) (a 17) 4 d17 c53 (by decide +kernel)
  have t6 : a 21 ∈ [0,1] := remove (a 21) 4 [0,1,4] t5 b6
  have b7 : a 20 ≠ 1 := exclude [0] (edge r61) (a 20) (a 22) 1 d22 c61 (by decide +kernel)
  have t7 : a 20 ∈ [0,8,9] := remove (a 20) 1 [0,1,8,9] d20 b7
  have b8 : a 20 ≠ 9 := exclude [0] (edge r61) (a 20) (a 22) 9 d22 c61 (by decide +kernel)
  have t8 : a 20 ∈ [0,8] := remove (a 20) 9 [0,8,9] t7 b8
  have b9 : a 21 ≠ 1 := exclude [0,2] (edge r63) (a 21) (a 23) 1 d23 c63 (by decide +kernel)
  have t9 : a 21 ∈ [0] := remove (a 21) 1 [0,1] t6 b9
  have b10 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 t9 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,3] := remove (a 29) 2 [0,1,2,3] d29 b10
  have b11 : a 29 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 3 t9 c64 (by decide +kernel)
  have t11 : a 29 ∈ [0,1] := remove (a 29) 3 [0,1,3] t10 b11
  have b12 : a 30 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,3] := remove (a 30) 1 [0,1,2,3] d30 b12
  have b13 : a 30 ≠ 3 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 3 d22 c66 (by decide +kernel)
  have t13 : a 30 ∈ [0,2] := remove (a 30) 3 [0,2,3] t12 b13
  have b14 : a 25 ≠ 1 := exclude [0,1] (edge r71) (a 25) (a 27) 1 d27 c71 (by decide +kernel)
  have t14 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b14
  have b15 : a 26 ≠ 1 := exclude [0,2] (edge r74) (a 26) (a 30) 1 t13 c74 (by decide +kernel)
  have t15 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b15
  exact And.intro t2 (And.intro t4 (And.intro t9 (And.intro t8 (And.intro t11 (And.intro t13 (And.intro t14 (t15)))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_177
