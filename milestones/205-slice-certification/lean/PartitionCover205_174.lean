import FiniteDomain205
namespace PartitionCover205_174
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[63]
def r3 : Array Nat := #[7]
def r4 : Array Nat := #[3]
def r5 : Array Nat := #[7]
def r6 : Array Nat := #[63]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[3]
def r9 : Array Nat := #[7]
def r10 : Array Nat := #[1]
def r11 : Array Nat := #[1]
def r12 : Array Nat := #[3]
def r13 : Array Nat := #[3,12,48]
def r14 : Array Nat := #[7,7,7]
def r15 : Array Nat := #[33,33,33]
def r16 : Array Nat := #[1,2,4,8,16,32]
def r17 : Array Nat := #[1,1,1,1,1,1]
def r18 : Array Nat := #[1,2,4,8,16,32]
def r19 : Array Nat := #[63,63,63,63,63,63]
def r20 : Array Nat := #[1,2,4,8,16,32]
def r21 : Array Nat := #[63,63,63,63,63,63]
def r22 : Array Nat := #[63]
def r23 : Array Nat := #[1]
def r24 : Array Nat := #[1]
def r25 : Array Nat := #[1,2,4,8,16,32]
def r26 : Array Nat := #[63,63,63,63,63,63]
def r27 : Array Nat := #[1,0,0]
def r28 : Array Nat := #[3,3,0]
def r29 : Array Nat := #[5,0,0]
def r30 : Array Nat := #[1,1,1]
def r31 : Array Nat := #[1]
def r32 : Array Nat := #[3]
def r33 : Array Nat := #[7,3,0,0]
def r34 : Array Nat := #[1,0,0,0]
def r35 : Array Nat := #[1,1,1,1]
def r36 : Array Nat := #[53,30,43]
def r37 : Array Nat := #[3,0,48]
def r38 : Array Nat := #[1,1,0,0,0,0]
def r39 : Array Nat := #[7,0,0,0,0,7]
def r40 : Array Nat := #[1]
def r41 : Array Nat := #[7]
def r42 : Array Nat := #[7,0,0,0,0,7]
def r43 : Array Nat := #[1,2]
def r44 : Array Nat := #[1,2]
def r45 : Array Nat := #[63,63]
def r46 : Array Nat := #[1,1]
def r47 : Array Nat := #[63,63]
def r48 : Array Nat := #[63,63]
def r49 : Array Nat := #[1,2]
def r50 : Array Nat := #[63,63]
def r51 : Array Nat := #[1,2]
def r52 : Array Nat := #[1,1]
def r53 : Array Nat := #[1,2,4,8,16,32]
def r54 : Array Nat := #[1,2,4,8,16,32]
def r55 : Array Nat := #[1,2,4,8,16,32]
def r56 : Array Nat := #[1,0,2,0,2,1]
def r57 : Array Nat := #[1,1,2,2,4,4]
def r58 : Array Nat := #[1,2,4,8,16,32]
def r59 : Array Nat := #[1,2,4,8,16,32]
def r60 : Array Nat := #[33,20]
def r61 : Array Nat := #[1,2]
def r62 : Array Nat := #[1,2,4,2,4,1]
def r63 : Array Nat := #[3]
def r64 : Array Nat := #[1]
def r65 : Array Nat := #[7]
def r66 : Array Nat := #[3,12]
def r67 : Array Nat := #[33,20]
def r68 : Array Nat := #[15]
def r69 : Array Nat := #[3]
def r70 : Array Nat := #[1,2,4,2,4,1]
def r71 : Array Nat := #[3,12,48]
def r72 : Array Nat := #[3,3,0]
def r73 : Array Nat := #[1,2,4,2,4,1]
def r74 : Array Nat := #[5,5,0]
theorem chunk0 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0])
    (d18 : a 18 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1,2])
    (d21 : a 21 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d8 : a 8 ∈ [0,1,2])
    (d9 : a 9 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0,1,2])
    (c11 : edge r11 (a 2) (a 10)=true)
    (c15 : edge r15 (a 3) (a 18)=true)
    (c24 : edge r24 (a 6) (a 21)=true)
    (c27 : edge r27 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 12)=true)
    (c31 : edge r31 (a 9) (a 11)=true)
    : a 10 ∈ [0] ∧ a 18 ∈ [0,5] ∧ a 21 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0,2] ∧ a 11 ∈ [0] := by
  have b0 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t0 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b0
  have b1 : a 10 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0,3] := remove (a 10) 2 [0,2,3] t0 b1
  have b2 : a 10 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 3 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 3 [0,3] t1 b2
  have b3 : a 18 ≠ 1 := exclude [0,1,2] (fun u v => edge r15 v u) (a 18) (a 3) 1 d3 c15 (by decide +kernel)
  have t3 : a 18 ∈ [0,2,3,4,5] := remove (a 18) 1 [0,1,2,3,4,5] d18 b3
  have b4 : a 18 ≠ 2 := exclude [0,1,2] (fun u v => edge r15 v u) (a 18) (a 3) 2 d3 c15 (by decide +kernel)
  have t4 : a 18 ∈ [0,3,4,5] := remove (a 18) 2 [0,2,3,4,5] t3 b4
  have b5 : a 18 ≠ 3 := exclude [0,1,2] (fun u v => edge r15 v u) (a 18) (a 3) 3 d3 c15 (by decide +kernel)
  have t5 : a 18 ∈ [0,4,5] := remove (a 18) 3 [0,3,4,5] t4 b5
  have b6 : a 18 ≠ 4 := exclude [0,1,2] (fun u v => edge r15 v u) (a 18) (a 3) 4 d3 c15 (by decide +kernel)
  have t6 : a 18 ∈ [0,5] := remove (a 18) 4 [0,4,5] t5 b6
  have b7 : a 21 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 21) (a 6) 1 d6 c24 (by decide +kernel)
  have t7 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b7
  have b8 : a 8 ≠ 1 := exclude [0] (edge r27) (a 8) (a 9) 1 d9 c27 (by decide +kernel)
  have t8 : a 8 ∈ [0,2] := remove (a 8) 1 [0,1,2] d8 b8
  have b9 : a 8 ≠ 2 := exclude [0] (edge r27) (a 8) (a 9) 2 d9 c27 (by decide +kernel)
  have t9 : a 8 ∈ [0] := remove (a 8) 2 [0,2] t8 b9
  have b10 : a 12 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 12) (a 8) 1 t9 c29 (by decide +kernel)
  have t10 : a 12 ∈ [0,2,3,4,5] := remove (a 12) 1 [0,1,2,3,4,5] d12 b10
  have b11 : a 12 ≠ 3 := exclude [0] (fun u v => edge r29 v u) (a 12) (a 8) 3 t9 c29 (by decide +kernel)
  have t11 : a 12 ∈ [0,2,4,5] := remove (a 12) 3 [0,2,3,4,5] t10 b11
  have b12 : a 12 ≠ 4 := exclude [0] (fun u v => edge r29 v u) (a 12) (a 8) 4 t9 c29 (by decide +kernel)
  have t12 : a 12 ∈ [0,2,5] := remove (a 12) 4 [0,2,4,5] t11 b12
  have b13 : a 12 ≠ 5 := exclude [0] (fun u v => edge r29 v u) (a 12) (a 8) 5 t9 c29 (by decide +kernel)
  have t13 : a 12 ∈ [0,2] := remove (a 12) 5 [0,2,5] t12 b13
  have b14 : a 11 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 11) (a 9) 1 d9 c31 (by decide +kernel)
  have t14 : a 11 ∈ [0,2] := remove (a 11) 1 [0,1,2] d11 b14
  have b15 : a 11 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 11) (a 9) 2 d9 c31 (by decide +kernel)
  have t15 : a 11 ∈ [0] := remove (a 11) 2 [0,2] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk1 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d11 : a 11 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,2])
    (d13 : a 13 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d18 : a 18 ∈ [0,5])
    (c36 : edge r36 (a 11) (a 14)=true)
    (c37 : edge r37 (a 11) (a 26)=true)
    (c38 : edge r38 (a 12) (a 13)=true)
    (c40 : edge r40 (a 13) (a 14)=true)
    (c51 : edge r51 (a 17) (a 21)=true)
    (c53 : edge r53 (a 18) (a 22)=true)
    (c54 : edge r54 (a 18) (a 26)=true)
    : a 14 ∈ [0] ∧ a 26 ∈ [0,1] ∧ a 12 ∈ [0] ∧ a 17 ∈ [0] ∧ a 22 ∈ [0,5] ∧ a 18 ∈ [0] := by
  have b0 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 11) 1 d11 c36 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b0
  have b1 : a 14 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 11) 3 d11 c36 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,4,5] := remove (a 14) 3 [0,2,3,4,5] t0 b1
  have b2 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 11) 2 d11 c37 (by decide +kernel)
  have t2 : a 26 ∈ [0,1,3,4,5] := remove (a 26) 2 [0,1,2,3,4,5] d26 b2
  have b3 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 11) 3 d11 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,4,5] := remove (a 26) 3 [0,1,3,4,5] t2 b3
  have b4 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 11) 4 d11 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,5] := remove (a 26) 4 [0,1,4,5] t3 b4
  have b5 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 11) 5 d11 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1] := remove (a 26) 5 [0,1,5] t4 b5
  have b6 : a 12 ≠ 2 := exclude [0] (edge r38) (a 12) (a 13) 2 d13 c38 (by decide +kernel)
  have t6 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b6
  have b7 : a 14 ≠ 2 := exclude [0] (fun u v => edge r40 v u) (a 14) (a 13) 2 d13 c40 (by decide +kernel)
  have t7 : a 14 ∈ [0,4,5] := remove (a 14) 2 [0,2,4,5] t1 b7
  have b8 : a 14 ≠ 4 := exclude [0] (fun u v => edge r40 v u) (a 14) (a 13) 4 d13 c40 (by decide +kernel)
  have t8 : a 14 ∈ [0,5] := remove (a 14) 4 [0,4,5] t7 b8
  have b9 : a 14 ≠ 5 := exclude [0] (fun u v => edge r40 v u) (a 14) (a 13) 5 d13 c40 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 5 [0,5] t8 b9
  have b10 : a 17 ≠ 1 := exclude [0] (edge r51) (a 17) (a 21) 1 d21 c51 (by decide +kernel)
  have t10 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b10
  have b11 : a 22 ≠ 1 := exclude [0,5] (fun u v => edge r53 v u) (a 22) (a 18) 1 d18 c53 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b11
  have b12 : a 22 ≠ 2 := exclude [0,5] (fun u v => edge r53 v u) (a 22) (a 18) 2 d18 c53 (by decide +kernel)
  have t12 : a 22 ∈ [0,3,4,5] := remove (a 22) 2 [0,2,3,4,5] t11 b12
  have b13 : a 22 ≠ 3 := exclude [0,5] (fun u v => edge r53 v u) (a 22) (a 18) 3 d18 c53 (by decide +kernel)
  have t13 : a 22 ∈ [0,4,5] := remove (a 22) 3 [0,3,4,5] t12 b13
  have b14 : a 22 ≠ 4 := exclude [0,5] (fun u v => edge r53 v u) (a 22) (a 18) 4 d18 c53 (by decide +kernel)
  have t14 : a 22 ∈ [0,5] := remove (a 22) 4 [0,4,5] t13 b14
  have b15 : a 18 ≠ 5 := exclude [0,1] (edge r54) (a 18) (a 26) 5 t5 c54 (by decide +kernel)
  have t15 : a 18 ∈ [0] := remove (a 18) 5 [0,5] d18 b15
  exact And.intro t9 (And.intro t5 (And.intro t6 (And.intro t10 (And.intro t14 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d21 : a 21 ∈ [0])
    (d27 : a 27 ∈ [0,1,2])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,5])
    (d28 : a 28 ∈ [0,1,2,3,4,5])
    (d29 : a 29 ∈ [0,1,2])
    (c54 : edge r54 (a 18) (a 26)=true)
    (c56 : edge r56 (a 19) (a 21)=true)
    (c57 : edge r57 (a 19) (a 27)=true)
    (c58 : edge r58 (a 20) (a 22)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    (c61 : edge r61 (a 21) (a 29)=true)
    : a 26 ∈ [0] ∧ a 19 ∈ [0,5] ∧ a 27 ∈ [0,2] ∧ a 20 ∈ [0,5] ∧ a 28 ∈ [0,5] ∧ a 29 ∈ [0] := by
  have b0 : a 26 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 26) (a 18) 1 d18 c54 (by decide +kernel)
  have t0 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b0
  have b1 : a 19 ≠ 1 := exclude [0] (edge r56) (a 19) (a 21) 1 d21 c56 (by decide +kernel)
  have t1 : a 19 ∈ [0,2,3,4,5] := remove (a 19) 1 [0,1,2,3,4,5] d19 b1
  have b2 : a 19 ≠ 2 := exclude [0] (edge r56) (a 19) (a 21) 2 d21 c56 (by decide +kernel)
  have t2 : a 19 ∈ [0,3,4,5] := remove (a 19) 2 [0,2,3,4,5] t1 b2
  have b3 : a 19 ≠ 3 := exclude [0] (edge r56) (a 19) (a 21) 3 d21 c56 (by decide +kernel)
  have t3 : a 19 ∈ [0,4,5] := remove (a 19) 3 [0,3,4,5] t2 b3
  have b4 : a 19 ≠ 4 := exclude [0] (edge r56) (a 19) (a 21) 4 d21 c56 (by decide +kernel)
  have t4 : a 19 ∈ [0,5] := remove (a 19) 4 [0,4,5] t3 b4
  have b5 : a 27 ≠ 1 := exclude [0,5] (fun u v => edge r57 v u) (a 27) (a 19) 1 t4 c57 (by decide +kernel)
  have t5 : a 27 ∈ [0,2] := remove (a 27) 1 [0,1,2] d27 b5
  have b6 : a 20 ≠ 1 := exclude [0,5] (edge r58) (a 20) (a 22) 1 d22 c58 (by decide +kernel)
  have t6 : a 20 ∈ [0,2,3,4,5] := remove (a 20) 1 [0,1,2,3,4,5] d20 b6
  have b7 : a 20 ≠ 2 := exclude [0,5] (edge r58) (a 20) (a 22) 2 d22 c58 (by decide +kernel)
  have t7 : a 20 ∈ [0,3,4,5] := remove (a 20) 2 [0,2,3,4,5] t6 b7
  have b8 : a 20 ≠ 3 := exclude [0,5] (edge r58) (a 20) (a 22) 3 d22 c58 (by decide +kernel)
  have t8 : a 20 ∈ [0,4,5] := remove (a 20) 3 [0,3,4,5] t7 b8
  have b9 : a 20 ≠ 4 := exclude [0,5] (edge r58) (a 20) (a 22) 4 d22 c58 (by decide +kernel)
  have t9 : a 20 ∈ [0,5] := remove (a 20) 4 [0,4,5] t8 b9
  have b10 : a 28 ≠ 1 := exclude [0,5] (fun u v => edge r59 v u) (a 28) (a 20) 1 t9 c59 (by decide +kernel)
  have t10 : a 28 ∈ [0,2,3,4,5] := remove (a 28) 1 [0,1,2,3,4,5] d28 b10
  have b11 : a 28 ≠ 2 := exclude [0,5] (fun u v => edge r59 v u) (a 28) (a 20) 2 t9 c59 (by decide +kernel)
  have t11 : a 28 ∈ [0,3,4,5] := remove (a 28) 2 [0,2,3,4,5] t10 b11
  have b12 : a 28 ≠ 3 := exclude [0,5] (fun u v => edge r59 v u) (a 28) (a 20) 3 t9 c59 (by decide +kernel)
  have t12 : a 28 ∈ [0,4,5] := remove (a 28) 3 [0,3,4,5] t11 b12
  have b13 : a 28 ≠ 4 := exclude [0,5] (fun u v => edge r59 v u) (a 28) (a 20) 4 t9 c59 (by decide +kernel)
  have t13 : a 28 ∈ [0,5] := remove (a 28) 4 [0,4,5] t12 b13
  have b14 : a 29 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 29) (a 21) 1 d21 c61 (by decide +kernel)
  have t14 : a 29 ∈ [0,2] := remove (a 29) 1 [0,1,2] d29 b14
  have b15 : a 29 ≠ 2 := exclude [0] (fun u v => edge r61 v u) (a 29) (a 21) 2 d21 c61 (by decide +kernel)
  have t15 : a 29 ∈ [0] := remove (a 29) 2 [0,2] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2])
    (d22 : a 22 ∈ [0,5])
    (d24 : a 24 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d27 : a 27 ∈ [0,2])
    (d29 : a 29 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d14 : a 14 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c25 : edge r25 (a 7) (a 14)=true)
    (c44 : edge r44 (a 15) (a 17)=true)
    (c49 : edge r49 (a 16) (a 24)=true)
    (c62 : edge r62 (a 22) (a 30)=true)
    (c66 : edge r66 (a 24) (a 26)=true)
    (c72 : edge r72 (a 27) (a 29)=true)
    : a 30 ∈ [0] ∧ a 24 ∈ [0] ∧ a 27 ∈ [0] ∧ a 4 ∈ [0] ∧ a 7 ∈ [0] ∧ a 15 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 30 ≠ 1 := exclude [0,5] (fun u v => edge r62 v u) (a 30) (a 22) 1 d22 c62 (by decide +kernel)
  have t0 : a 30 ∈ [0,2] := remove (a 30) 1 [0,1,2] d30 b0
  have b1 : a 30 ≠ 2 := exclude [0,5] (fun u v => edge r62 v u) (a 30) (a 22) 2 d22 c62 (by decide +kernel)
  have t1 : a 30 ∈ [0] := remove (a 30) 2 [0,2] t0 b1
  have b2 : a 24 ≠ 1 := exclude [0] (edge r66) (a 24) (a 26) 1 d26 c66 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b2
  have b3 : a 27 ≠ 2 := exclude [0] (edge r72) (a 27) (a 29) 2 d29 c72 (by decide +kernel)
  have t3 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b3
  have b4 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b4
  have b5 : a 4 ≠ 2 := exclude [0] (edge r18) (a 4) (a 12) 2 d12 c18 (by decide +kernel)
  have t5 : a 4 ∈ [0,3,4,5] := remove (a 4) 2 [0,2,3,4,5] t4 b5
  have b6 : a 4 ≠ 3 := exclude [0] (edge r18) (a 4) (a 12) 3 d12 c18 (by decide +kernel)
  have t6 : a 4 ∈ [0,4,5] := remove (a 4) 3 [0,3,4,5] t5 b6
  have b7 : a 4 ≠ 4 := exclude [0] (edge r18) (a 4) (a 12) 4 d12 c18 (by decide +kernel)
  have t7 : a 4 ∈ [0,5] := remove (a 4) 4 [0,4,5] t6 b7
  have b8 : a 4 ≠ 5 := exclude [0] (edge r18) (a 4) (a 12) 5 d12 c18 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 5 [0,5] t7 b8
  have b9 : a 7 ≠ 1 := exclude [0] (edge r25) (a 7) (a 14) 1 d14 c25 (by decide +kernel)
  have t9 : a 7 ∈ [0,2,3,4,5] := remove (a 7) 1 [0,1,2,3,4,5] d7 b9
  have b10 : a 7 ≠ 2 := exclude [0] (edge r25) (a 7) (a 14) 2 d14 c25 (by decide +kernel)
  have t10 : a 7 ∈ [0,3,4,5] := remove (a 7) 2 [0,2,3,4,5] t9 b10
  have b11 : a 7 ≠ 3 := exclude [0] (edge r25) (a 7) (a 14) 3 d14 c25 (by decide +kernel)
  have t11 : a 7 ∈ [0,4,5] := remove (a 7) 3 [0,3,4,5] t10 b11
  have b12 : a 7 ≠ 4 := exclude [0] (edge r25) (a 7) (a 14) 4 d14 c25 (by decide +kernel)
  have t12 : a 7 ∈ [0,5] := remove (a 7) 4 [0,4,5] t11 b12
  have b13 : a 7 ≠ 5 := exclude [0] (edge r25) (a 7) (a 14) 5 d14 c25 (by decide +kernel)
  have t13 : a 7 ∈ [0] := remove (a 7) 5 [0,5] t12 b13
  have b14 : a 15 ≠ 1 := exclude [0] (edge r44) (a 15) (a 17) 1 d17 c44 (by decide +kernel)
  have t14 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b14
  have b15 : a 16 ≠ 1 := exclude [0] (edge r49) (a 16) (a 24) 1 t2 c49 (by decide +kernel)
  have t15 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b15
  exact And.intro t1 (And.intro t2 (And.intro t3 (And.intro t8 (And.intro t13 (And.intro t14 (t15))))))

theorem chunk4 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,5])
    (d18 : a 18 ∈ [0])
    (d19 : a 19 ∈ [0,5])
    (d27 : a 27 ∈ [0])
    (d20 : a 20 ∈ [0,5])
    (d28 : a 28 ∈ [0,5])
    (d3 : a 3 ∈ [0,1,2])
    (d7 : a 7 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c53 : edge r53 (a 18) (a 22)=true)
    (c57 : edge r57 (a 19) (a 27)=true)
    (c58 : edge r58 (a 20) (a 22)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    : a 22 ∈ [0] ∧ a 19 ∈ [0] ∧ a 20 ∈ [0] ∧ a 28 ∈ [0] ∧ a 3 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 22 ≠ 5 := exclude [0] (fun u v => edge r53 v u) (a 22) (a 18) 5 d18 c53 (by decide +kernel)
  have t0 : a 22 ∈ [0] := remove (a 22) 5 [0,5] d22 b0
  have b1 : a 19 ≠ 5 := exclude [0] (edge r57) (a 19) (a 27) 5 d27 c57 (by decide +kernel)
  have t1 : a 19 ∈ [0] := remove (a 19) 5 [0,5] d19 b1
  have b2 : a 20 ≠ 5 := exclude [0] (edge r58) (a 20) (a 22) 5 t0 c58 (by decide +kernel)
  have t2 : a 20 ∈ [0] := remove (a 20) 5 [0,5] d20 b2
  have b3 : a 28 ≠ 5 := exclude [0] (fun u v => edge r59 v u) (a 28) (a 20) 5 t2 c59 (by decide +kernel)
  have t3 : a 28 ∈ [0] := remove (a 28) 5 [0,5] d28 b3
  have b4 : a 3 ≠ 1 := exclude [0] (edge r13) (a 3) (a 7) 1 d7 c13 (by decide +kernel)
  have t4 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b4
  have b5 : a 3 ≠ 2 := exclude [0] (edge r13) (a 3) (a 7) 2 d7 c13 (by decide +kernel)
  have t5 : a 3 ∈ [0] := remove (a 3) 2 [0,2] t4 b5
  have b6 : a 5 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b6
  have b7 : a 5 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 2 d4 c16 (by decide +kernel)
  have t7 : a 5 ∈ [0,3,4,5] := remove (a 5) 2 [0,2,3,4,5] t6 b7
  have b8 : a 5 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t8 : a 5 ∈ [0,4,5] := remove (a 5) 3 [0,3,4,5] t7 b8
  have b9 : a 5 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 4 d4 c16 (by decide +kernel)
  have t9 : a 5 ∈ [0,5] := remove (a 5) 4 [0,4,5] t8 b9
  have b10 : a 5 ≠ 5 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 5 d4 c16 (by decide +kernel)
  have t10 : a 5 ∈ [0] := remove (a 5) 5 [0,5] t9 b10
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t5 (t10)))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1,2])
    (start9 : a 9 ∈ [0])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0])
    (start14 : a 14 ∈ [0,1,2,3,4,5])
    (start15 : a 15 ∈ [0,1])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1,2,3,4,5])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0])
    (start26 : a 26 ∈ [0,1,2,3,4,5])
    (start27 : a 27 ∈ [0,1,2])
    (start28 : a 28 ∈ [0,1,2,3,4,5])
    (start29 : a 29 ∈ [0,1,2])
    (start30 : a 30 ∈ [0,1,2])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 15)=true)
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 16)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 17)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 18)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 19)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 20)=true)
    (c22 : edge r22 (a 6) (a 7)=true)
    (c23 : edge r23 (a 6) (a 13)=true)
    (c24 : edge r24 (a 6) (a 21)=true)
    (c25 : edge r25 (a 7) (a 14)=true)
    (c26 : edge r26 (a 7) (a 22)=true)
    (c27 : edge r27 (a 8) (a 9)=true)
    (c28 : edge r28 (a 8) (a 10)=true)
    (c29 : edge r29 (a 8) (a 12)=true)
    (c30 : edge r30 (a 8) (a 23)=true)
    (c31 : edge r31 (a 9) (a 11)=true)
    (c32 : edge r32 (a 9) (a 24)=true)
    (c33 : edge r33 (a 10) (a 11)=true)
    (c34 : edge r34 (a 10) (a 13)=true)
    (c35 : edge r35 (a 10) (a 25)=true)
    (c36 : edge r36 (a 11) (a 14)=true)
    (c37 : edge r37 (a 11) (a 26)=true)
    (c38 : edge r38 (a 12) (a 13)=true)
    (c39 : edge r39 (a 12) (a 27)=true)
    (c40 : edge r40 (a 13) (a 14)=true)
    (c41 : edge r41 (a 13) (a 29)=true)
    (c42 : edge r42 (a 14) (a 30)=true)
    (c43 : edge r43 (a 15) (a 16)=true)
    (c44 : edge r44 (a 15) (a 17)=true)
    (c45 : edge r45 (a 15) (a 19)=true)
    (c46 : edge r46 (a 15) (a 23)=true)
    (c47 : edge r47 (a 16) (a 18)=true)
    (c48 : edge r48 (a 16) (a 20)=true)
    (c49 : edge r49 (a 16) (a 24)=true)
    (c50 : edge r50 (a 17) (a 18)=true)
    (c51 : edge r51 (a 17) (a 21)=true)
    (c52 : edge r52 (a 17) (a 25)=true)
    (c53 : edge r53 (a 18) (a 22)=true)
    (c54 : edge r54 (a 18) (a 26)=true)
    (c55 : edge r55 (a 19) (a 20)=true)
    (c56 : edge r56 (a 19) (a 21)=true)
    (c57 : edge r57 (a 19) (a 27)=true)
    (c58 : edge r58 (a 20) (a 22)=true)
    (c59 : edge r59 (a 20) (a 28)=true)
    (c60 : edge r60 (a 21) (a 22)=true)
    (c61 : edge r61 (a 21) (a 29)=true)
    (c62 : edge r62 (a 22) (a 30)=true)
    (c63 : edge r63 (a 23) (a 24)=true)
    (c64 : edge r64 (a 23) (a 25)=true)
    (c65 : edge r65 (a 23) (a 27)=true)
    (c66 : edge r66 (a 24) (a 26)=true)
    (c67 : edge r67 (a 24) (a 28)=true)
    (c68 : edge r68 (a 25) (a 26)=true)
    (c69 : edge r69 (a 25) (a 29)=true)
    (c70 : edge r70 (a 26) (a 30)=true)
    (c71 : edge r71 (a 27) (a 28)=true)
    (c72 : edge r72 (a 27) (a 29)=true)
    (c73 : edge r73 (a 28) (a 30)=true)
    (c74 : edge r74 (a 29) (a 30)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0) := by
  have group1 := chunk0 a start10 start2 start18 start3 start21 start6 start8 start9 start12 start11 c11 c15 c24 c27 c29 c31
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7⟩
  have group8 := chunk1 a start14 h7 start26 h6 start13 start17 h4 start22 h3 c36 c37 c38 c40 c51 c53 c54
  rcases group8 with ⟨h9,h10,h11,h12,h13,h14⟩
  have group15 := chunk2 a h10 h14 start19 h4 start27 start20 h13 start28 start29 c54 c56 c57 c58 c59 c61
  rcases group15 with ⟨h16,h17,h18,h19,h20,h21⟩
  have group22 := chunk3 a start30 h13 start24 h16 h18 h21 start4 h11 start7 h9 start15 h12 start16 c18 c25 c44 c49 c62 c66 c72
  rcases group22 with ⟨h23,h24,h25,h26,h27,h28,h29⟩
  have group30 := chunk4 a h13 h14 h17 h25 h19 h20 start3 h27 start5 h26 c13 c16 c53 c57 c58 c59
  rcases group30 with ⟨h31,h32,h33,h34,h35,h36⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h35) (And.intro (forced (a 4) 0 h26) (And.intro (forced (a 5) 0 h36) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 h27) (And.intro (forced (a 8) 0 h5) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 0 h2) (And.intro (forced (a 11) 0 h7) (And.intro (forced (a 12) 0 h11) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 0 h9) (And.intro (forced (a 15) 0 h28) (And.intro (forced (a 16) 0 h29) (And.intro (forced (a 17) 0 h12) (And.intro (forced (a 18) 0 h14) (And.intro (forced (a 19) 0 h32) (And.intro (forced (a 20) 0 h33) (And.intro (forced (a 21) 0 h4) (And.intro (forced (a 22) 0 h31) (And.intro (forced (a 23) 0 start23) (And.intro (forced (a 24) 0 h24) (And.intro (forced (a 25) 0 start25) (And.intro (forced (a 26) 0 h16) (And.intro (forced (a 27) 0 h25) (And.intro (forced (a 28) 0 h34) (And.intro (forced (a 29) 0 h21) (forced (a 30) 0 h23))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_174
