import FiniteDomain205
namespace PartitionCover205_165
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[5]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[1]
def r5 : Array Nat := #[1]
def r6 : Array Nat := #[1]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[1]
def r10 : Array Nat := #[3]
def r11 : Array Nat := #[7]
def r12 : Array Nat := #[1]
def r13 : Array Nat := #[1]
def r14 : Array Nat := #[1]
def r15 : Array Nat := #[1]
def r16 : Array Nat := #[3,12,48,192]
def r17 : Array Nat := #[1,2,1,2]
def r18 : Array Nat := #[1,1,2,2]
def r19 : Array Nat := #[63,0,63,0]
def r20 : Array Nat := #[1,0,0,0,2,0,0,0]
def r21 : Array Nat := #[3,0,3,0,3,0,3,0]
def r22 : Array Nat := #[1,32,1,0,2,8,2,0]
def r23 : Array Nat := #[3,3]
def r24 : Array Nat := #[5,10]
def r25 : Array Nat := #[43,43]
def r26 : Array Nat := #[1,2]
def r27 : Array Nat := #[3,5]
def r28 : Array Nat := #[1]
def r29 : Array Nat := #[1]
def r30 : Array Nat := #[3]
def r31 : Array Nat := #[3]
def r32 : Array Nat := #[1]
def r33 : Array Nat := #[3]
def r34 : Array Nat := #[5]
def r35 : Array Nat := #[1,0,0]
def r36 : Array Nat := #[3,0,0]
def r37 : Array Nat := #[1,0,0]
def r38 : Array Nat := #[3]
def r39 : Array Nat := #[3]
def r40 : Array Nat := #[1,2]
def r41 : Array Nat := #[3,12]
def r42 : Array Nat := #[1,1]
def r43 : Array Nat := #[1,2]
def r44 : Array Nat := #[63,63]
def r45 : Array Nat := #[3,0,3,0]
def r46 : Array Nat := #[3,5,24,40]
def r47 : Array Nat := #[7,7]
def r48 : Array Nat := #[1]
def r49 : Array Nat := #[1]
def r50 : Array Nat := #[63]
def r51 : Array Nat := #[3]
def r52 : Array Nat := #[3]
def r53 : Array Nat := #[3]
def r54 : Array Nat := #[5]
def r55 : Array Nat := #[3]
def r56 : Array Nat := #[43]
def r57 : Array Nat := #[3]
def r58 : Array Nat := #[3,5]
def r59 : Array Nat := #[1,2]
def r60 : Array Nat := #[1,2,4,8,16,32]
def r61 : Array Nat := #[1,2,4,8,16,32]
def r62 : Array Nat := #[1,1,2,2,4,4]
def r63 : Array Nat := #[1,1,2,2,4,4]
def r64 : Array Nat := #[1,2,4,8,16,32]
def r65 : Array Nat := #[5,3,6,3,6,5]
def r66 : Array Nat := #[1,8,18,8,18,1]
def r67 : Array Nat := #[7,0,0]
def r68 : Array Nat := #[3,12]
def r69 : Array Nat := #[1,2]
def r70 : Array Nat := #[3,5]
def r71 : Array Nat := #[1,0,2,0]
def r72 : Array Nat := #[1,4,2,16]
def r73 : Array Nat := #[1,2]
def r74 : Array Nat := #[7,56]
def r75 : Array Nat := #[3,5]
def r76 : Array Nat := #[3,12,48]
def r77 : Array Nat := #[9,2,16]
def r78 : Array Nat := #[1,1,0,0,0,0]
def r79 : Array Nat := #[5,0,5,3,0,3]
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (d1 : a 1 ∈ [0])
    (d7 : a 7 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d19 : a 19 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    : a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 7 ∈ [0] ∧ a 19 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 21 ∈ [0,3,4,5] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t0 b1
  have b2 : a 5 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t2 : a 5 ∈ [0,2,3,4,5,6,7] := remove (a 5) 1 [0,1,2,3,4,5,6,7] d5 b2
  have b3 : a 5 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 2 d1 c6 (by decide +kernel)
  have t3 : a 5 ∈ [0,3,4,5,6,7] := remove (a 5) 2 [0,2,3,4,5,6,7] t2 b3
  have b4 : a 5 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t4 : a 5 ∈ [0,4,5,6,7] := remove (a 5) 3 [0,3,4,5,6,7] t3 b4
  have b5 : a 5 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 4 d1 c6 (by decide +kernel)
  have t5 : a 5 ∈ [0,5,6,7] := remove (a 5) 4 [0,4,5,6,7] t4 b5
  have b6 : a 5 ≠ 5 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 5 d1 c6 (by decide +kernel)
  have t6 : a 5 ∈ [0,6,7] := remove (a 5) 5 [0,5,6,7] t5 b6
  have b7 : a 5 ≠ 6 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 6 d1 c6 (by decide +kernel)
  have t7 : a 5 ∈ [0,7] := remove (a 5) 6 [0,6,7] t6 b7
  have b8 : a 5 ≠ 7 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 7 d1 c6 (by decide +kernel)
  have t8 : a 5 ∈ [0] := remove (a 5) 7 [0,7] t7 b8
  have b9 : a 7 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 1 d3 c13 (by decide +kernel)
  have t9 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b9
  have b10 : a 19 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t10 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b10
  have b11 : a 4 ≠ 2 := exclude [0] (edge r16) (a 4) (a 5) 2 t8 c16 (by decide +kernel)
  have t11 : a 4 ∈ [0] := remove (a 4) 2 [0,2] t1 b11
  have b12 : a 6 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 1 t11 c17 (by decide +kernel)
  have t12 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b12
  have b13 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t11 c18 (by decide +kernel)
  have t13 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b13
  have b14 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 t8 c22 (by decide +kernel)
  have t14 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b14
  have b15 : a 21 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 2 t8 c22 (by decide +kernel)
  have t15 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t14 b15
  exact And.intro t11 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,3,4,5])
    (d5 : a 5 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1])
    (d7 : a 7 ∈ [0])
    (d23 : a 23 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,1,2])
    (d8 : a 8 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    : a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0,1,3,5] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0,1] ∧ a 10 ∈ [0] ∧ a 25 ∈ [0,2] ∧ a 26 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 21 ≠ 3 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 3 d5 c22 (by decide +kernel)
  have t0 : a 21 ∈ [0,4,5] := remove (a 21) 3 [0,3,4,5] d21 b0
  have b1 : a 21 ≠ 4 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t1 : a 21 ∈ [0,5] := remove (a 21) 4 [0,4,5] t0 b1
  have b2 : a 21 ≠ 5 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t2 : a 21 ∈ [0] := remove (a 21) 5 [0,5] t1 b2
  have b3 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b3
  have b4 : a 14 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t3 b4
  have b5 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t5 : a 22 ∈ [0,1,3,4,5] := remove (a 22) 2 [0,1,2,3,4,5] d22 b5
  have b6 : a 22 ≠ 4 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t6 : a 22 ∈ [0,1,3,5] := remove (a 22) 4 [0,1,3,4,5] t5 b6
  have b7 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 d7 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b7
  have b8 : a 23 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t8 : a 23 ∈ [0,1] := remove (a 23) 2 [0,1,2] d23 b8
  have b9 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 d8 c29 (by decide +kernel)
  have t9 : a 10 ∈ [0,2] := remove (a 10) 1 [0,1,2] d10 b9
  have b10 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 2 [0,2] t9 b10
  have b11 : a 25 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b11
  have b12 : a 25 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t11 b12
  have b13 : a 14 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 2 t10 c36 (by decide +kernel)
  have t13 : a 14 ∈ [0] := remove (a 14) 2 [0,2] t4 b13
  have b14 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b14
  have b15 : a 13 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 1 d12 c40 (by decide +kernel)
  have t15 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b15
  exact And.intro t2 (And.intro t13 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,2])
    (d12 : a 12 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0])
    (d27 : a 27 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d21 : a 21 ∈ [0])
    (d22 : a 22 ∈ [0,1,3,5])
    (d23 : a 23 ∈ [0,1])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    : a 28 ∈ [0] ∧ a 30 ∈ [0,1] ∧ a 27 ∈ [0] ∧ a 20 ∈ [0] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0] := by
  have b0 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2] := remove (a 28) 1 [0,1,2] d28 b0
  have b1 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 2 [0,2] t0 b1
  have b2 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0,1,3,4,5] := remove (a 30) 2 [0,1,2,3,4,5] d30 b2
  have b3 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [0,1,4,5] := remove (a 30) 3 [0,1,3,4,5] t2 b3
  have b4 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,5] := remove (a 30) 4 [0,1,4,5] t3 b4
  have b5 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1] := remove (a 30) 5 [0,1,5] t4 b5
  have b6 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t6 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b6
  have b7 : a 20 ≠ 1 := exclude [0] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t7 : a 20 ∈ [0,2,3,4,5] := remove (a 20) 1 [0,1,2,3,4,5] d20 b7
  have b8 : a 20 ≠ 2 := exclude [0] (edge r60) (a 20) (a 21) 2 d21 c60 (by decide +kernel)
  have t8 : a 20 ∈ [0,3,4,5] := remove (a 20) 2 [0,2,3,4,5] t7 b8
  have b9 : a 20 ≠ 3 := exclude [0] (edge r60) (a 20) (a 21) 3 d21 c60 (by decide +kernel)
  have t9 : a 20 ∈ [0,4,5] := remove (a 20) 3 [0,3,4,5] t8 b9
  have b10 : a 20 ≠ 4 := exclude [0] (edge r60) (a 20) (a 21) 4 d21 c60 (by decide +kernel)
  have t10 : a 20 ∈ [0,5] := remove (a 20) 4 [0,4,5] t9 b10
  have b11 : a 20 ≠ 5 := exclude [0] (edge r60) (a 20) (a 21) 5 d21 c60 (by decide +kernel)
  have t11 : a 20 ∈ [0] := remove (a 20) 5 [0,5] t10 b11
  have b12 : a 22 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 1 t11 c61 (by decide +kernel)
  have t12 : a 22 ∈ [0,3,5] := remove (a 22) 1 [0,1,3,5] d22 b12
  have b13 : a 22 ≠ 3 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 3 t11 c61 (by decide +kernel)
  have t13 : a 22 ∈ [0,5] := remove (a 22) 3 [0,3,5] t12 b13
  have b14 : a 22 ≠ 5 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 5 t11 c61 (by decide +kernel)
  have t14 : a 22 ∈ [0] := remove (a 22) 5 [0,5] t13 b14
  have b15 : a 23 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 1 d21 c63 (by decide +kernel)
  have t15 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b15
  exact And.intro t1 (And.intro t5 (And.intro t6 (And.intro t11 (And.intro t14 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d21 : a 21 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d25 : a 25 ∈ [0,2])
    (d27 : a 27 ∈ [0])
    (d31 : a 31 ∈ [0,1,2])
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 31 ∈ [0] := by
  have b0 : a 29 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 1 d21 c64 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,3,4,5] := remove (a 29) 1 [0,1,2,3,4,5] d29 b0
  have b1 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0,3,4,5] := remove (a 29) 2 [0,2,3,4,5] t0 b1
  have b2 : a 29 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 3 d21 c64 (by decide +kernel)
  have t2 : a 29 ∈ [0,4,5] := remove (a 29) 3 [0,3,4,5] t1 b2
  have b3 : a 29 ≠ 4 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 4 d21 c64 (by decide +kernel)
  have t3 : a 29 ∈ [0,5] := remove (a 29) 4 [0,4,5] t2 b3
  have b4 : a 29 ≠ 5 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 5 d21 c64 (by decide +kernel)
  have t4 : a 29 ∈ [0] := remove (a 29) 5 [0,5] t3 b4
  have b5 : a 30 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t5 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b5
  have b6 : a 24 ≠ 1 := exclude [0] (edge r69) (a 24) (a 26) 1 d26 c69 (by decide +kernel)
  have t6 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b6
  have b7 : a 25 ≠ 2 := exclude [0] (edge r71) (a 25) (a 27) 2 d27 c71 (by decide +kernel)
  have t7 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b7
  have b8 : a 31 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 2 d27 c75 (by decide +kernel)
  have t8 : a 31 ∈ [0,1] := remove (a 31) 2 [0,1,2] d31 b8
  have b9 : a 31 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 31) (a 29) 1 t4 c78 (by decide +kernel)
  have t9 : a 31 ∈ [0] := remove (a 31) 1 [0,1] t8 b9
  exact And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t9))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0])
    (start9 : a 9 ∈ [0])
    (start10 : a 10 ∈ [0,1,2])
    (start11 : a 11 ∈ [0])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1])
    (start16 : a 16 ∈ [0])
    (start17 : a 17 ∈ [0])
    (start18 : a 18 ∈ [0])
    (start19 : a 19 ∈ [0,1])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0,1,2])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0,1,2,3])
    (start26 : a 26 ∈ [0,1])
    (start27 : a 27 ∈ [0,1])
    (start28 : a 28 ∈ [0,1,2])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2,3,4,5])
    (start31 : a 31 ∈ [0,1,2])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
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
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) := by
  have group1 := chunk0 a start4 start0 start5 start1 start7 start3 start19 start6 start12 start21 c2 c6 c13 c15 c16 c17 c18 c22
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have group9 := chunk1 a h8 h3 start14 h6 start22 start15 h4 start23 start10 start8 start25 start9 start26 start13 h7 c22 c24 c25 c26 c27 c29 c34 c36 c37 c40
  rcases group9 with ⟨h10,h11,h12,h13,h14,h15,h16,h17,h18⟩
  have group19 := chunk2 a start28 h7 start30 h11 start27 h5 start20 h10 h12 h14 c42 c46 c59 c60 c61 c63
  rcases group19 with ⟨h20,h21,h22,h23,h24,h25⟩
  have group26 := chunk3 a start29 h10 h21 h24 start24 h17 h16 h22 start31 c64 c66 c69 c71 c75 c78
  rcases group26 with ⟨h27,h28,h29,h30,h31⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h2) (And.intro (forced (a 5) 0 h3) (And.intro (forced (a 6) 0 h6) (And.intro (forced (a 7) 0 h4) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 0 h15) (And.intro (forced (a 11) 0 start11) (And.intro (forced (a 12) 0 h7) (And.intro (forced (a 13) 0 h18) (And.intro (forced (a 14) 0 h11) (And.intro (forced (a 15) 0 h13) (And.intro (forced (a 16) 0 start16) (And.intro (forced (a 17) 0 start17) (And.intro (forced (a 18) 0 start18) (And.intro (forced (a 19) 0 h5) (And.intro (forced (a 20) 0 h23) (And.intro (forced (a 21) 0 h10) (And.intro (forced (a 22) 0 h24) (And.intro (forced (a 23) 0 h25) (And.intro (forced (a 24) 0 h29) (And.intro (forced (a 25) 0 h30) (And.intro (forced (a 26) 0 h17) (And.intro (forced (a 27) 0 h22) (And.intro (forced (a 28) 0 h20) (And.intro (forced (a 29) 0 h27) (And.intro (forced (a 30) 0 h28) (forced (a 31) 0 h31)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_165
