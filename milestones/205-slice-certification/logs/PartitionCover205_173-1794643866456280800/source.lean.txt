import FiniteDomain205
namespace PartitionCover205_173
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[63]
def r3 : Array Nat := #[1]
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
def r14 : Array Nat := #[9,9,9]
def r15 : Array Nat := #[3,3,3]
def r16 : Array Nat := #[1,2,4,8,16,32]
def r17 : Array Nat := #[1,1,1,1,1,1]
def r18 : Array Nat := #[1,2,4,8,16,32]
def r19 : Array Nat := #[3,3,3,3,3,3]
def r20 : Array Nat := #[1,0,4,0,0,0]
def r21 : Array Nat := #[1,1,1,1,1,1]
def r22 : Array Nat := #[3,3,3,3,3,3]
def r23 : Array Nat := #[5]
def r24 : Array Nat := #[7]
def r25 : Array Nat := #[1]
def r26 : Array Nat := #[3,12,48,192,768,3072]
def r27 : Array Nat := #[3,3,3,3,3,3]
def r28 : Array Nat := #[1]
def r29 : Array Nat := #[1]
def r30 : Array Nat := #[63]
def r31 : Array Nat := #[1]
def r32 : Array Nat := #[1]
def r33 : Array Nat := #[1]
def r34 : Array Nat := #[3]
def r35 : Array Nat := #[3]
def r36 : Array Nat := #[3]
def r37 : Array Nat := #[1]
def r38 : Array Nat := #[2815,15,240,4090,3840,240]
def r39 : Array Nat := #[1,1,1,2,2,2]
def r40 : Array Nat := #[1,1,1,1,1,1]
def r41 : Array Nat := #[1,2,4,4,2,1]
def r42 : Array Nat := #[1,0,0,0,0,1]
def r43 : Array Nat := #[51]
def r44 : Array Nat := #[61]
def r45 : Array Nat := #[15,2815,240]
def r46 : Array Nat := #[13,12,0]
def r47 : Array Nat := #[1,0,1,0,0,0,0,0,2,0,2,0]
def r48 : Array Nat := #[1,2]
def r49 : Array Nat := #[1,2]
def r50 : Array Nat := #[3,3]
def r51 : Array Nat := #[3,3]
def r52 : Array Nat := #[3,3]
def r53 : Array Nat := #[3,3]
def r54 : Array Nat := #[1,2]
def r55 : Array Nat := #[3,3]
def r56 : Array Nat := #[1,2]
def r57 : Array Nat := #[1,1]
def r58 : Array Nat := #[1,2]
def r59 : Array Nat := #[1,2]
def r60 : Array Nat := #[1,2]
def r61 : Array Nat := #[3,3]
def r62 : Array Nat := #[1,2]
def r63 : Array Nat := #[1,2]
def r64 : Array Nat := #[7,56]
def r65 : Array Nat := #[3,3]
def r66 : Array Nat := #[3,12]
def r67 : Array Nat := #[3,3]
def r68 : Array Nat := #[3,3]
def r69 : Array Nat := #[1,1]
def r70 : Array Nat := #[1,2]
def r71 : Array Nat := #[1,0]
def r72 : Array Nat := #[9,2]
def r73 : Array Nat := #[3]
def r74 : Array Nat := #[7]
def r75 : Array Nat := #[1,2]
def r76 : Array Nat := #[7,56]
def r77 : Array Nat := #[5,2]
def r78 : Array Nat := #[3,1,3,3,2,3]
def r79 : Array Nat := #[3,3,1,0]
theorem chunk0 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1,2])
    (d5 : a 5 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d22 : a 22 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 11 ∈ [0,3] ∧ a 5 ∈ [0,2] ∧ a 7 ∈ [0,2] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0,1,4,5,7,8,9,10,11] := by
  have b0 : a 11 ≠ 1 := exclude [0,1,2] (fun u v => edge r14 v u) (a 11) (a 3) 1 d3 c14 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b0
  have b1 : a 11 ≠ 2 := exclude [0,1,2] (fun u v => edge r14 v u) (a 11) (a 3) 2 d3 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,3,4,5] := remove (a 11) 2 [0,2,3,4,5] t0 b1
  have b2 : a 11 ≠ 4 := exclude [0,1,2] (fun u v => edge r14 v u) (a 11) (a 3) 4 d3 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,3,5] := remove (a 11) 4 [0,3,4,5] t1 b2
  have b3 : a 11 ≠ 5 := exclude [0,1,2] (fun u v => edge r14 v u) (a 11) (a 3) 5 d3 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,3] := remove (a 11) 5 [0,3,5] t2 b3
  have b4 : a 5 ≠ 1 := exclude [0,1,2,3,4,5] (edge r20) (a 5) (a 7) 1 d7 c20 (by decide +kernel)
  have t4 : a 5 ∈ [0,2,3,4,5] := remove (a 5) 1 [0,1,2,3,4,5] d5 b4
  have b5 : a 5 ≠ 3 := exclude [0,1,2,3,4,5] (edge r20) (a 5) (a 7) 3 d7 c20 (by decide +kernel)
  have t5 : a 5 ∈ [0,2,4,5] := remove (a 5) 3 [0,2,3,4,5] t4 b5
  have b6 : a 5 ≠ 4 := exclude [0,1,2,3,4,5] (edge r20) (a 5) (a 7) 4 d7 c20 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,5] := remove (a 5) 4 [0,2,4,5] t5 b6
  have b7 : a 5 ≠ 5 := exclude [0,1,2,3,4,5] (edge r20) (a 5) (a 7) 5 d7 c20 (by decide +kernel)
  have t7 : a 5 ∈ [0,2] := remove (a 5) 5 [0,2,5] t6 b7
  have b8 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 1 t7 c20 (by decide +kernel)
  have t8 : a 7 ∈ [0,2,3,4,5] := remove (a 7) 1 [0,1,2,3,4,5] d7 b8
  have b9 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 3 t7 c20 (by decide +kernel)
  have t9 : a 7 ∈ [0,2,4,5] := remove (a 7) 3 [0,2,3,4,5] t8 b9
  have b10 : a 7 ≠ 4 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 4 t7 c20 (by decide +kernel)
  have t10 : a 7 ∈ [0,2,5] := remove (a 7) 4 [0,2,4,5] t9 b10
  have b11 : a 7 ≠ 5 := exclude [0,2] (fun u v => edge r20 v u) (a 7) (a 5) 5 t7 c20 (by decide +kernel)
  have t11 : a 7 ∈ [0,2] := remove (a 7) 5 [0,2,5] t10 b11
  have b12 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b12
  have b13 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 2 t11 c26 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b13
  have b14 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 t11 c26 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 15) 3 [0,1,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 6 t11 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 15) 6 [0,1,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t7 (And.intro t11 (And.intro t12 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,4,5,7,8,9,10,11])
    (d7 : a 7 ∈ [0,2])
    (d24 : a 24 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d11 : a 11 ∈ [0,3])
    (d9 : a 9 ∈ [0])
    (d14 : a 14 ∈ [0,1,2])
    (d10 : a 10 ∈ [0])
    (d27 : a 27 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 15 ∈ [0,1,4,5] ∧ a 24 ∈ [0] ∧ a 11 ∈ [0] ∧ a 14 ∈ [0,1] ∧ a 27 ∈ [0] ∧ a 12 ∈ [0,5] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0,2,3,4,5] ∧ a 30 ∈ [0,2,3] := by
  have b0 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 7 d7 c26 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,4,5,8,9,10,11] := remove (a 15) 7 [0,1,4,5,7,8,9,10,11] d15 b0
  have b1 : a 15 ≠ 8 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 8 d7 c26 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,4,5,9,10,11] := remove (a 15) 8 [0,1,4,5,8,9,10,11] t0 b1
  have b2 : a 15 ≠ 9 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 9 d7 c26 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,4,5,10,11] := remove (a 15) 9 [0,1,4,5,9,10,11] t1 b2
  have b3 : a 15 ≠ 10 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 10 d7 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0,1,4,5,11] := remove (a 15) 10 [0,1,4,5,10,11] t2 b3
  have b4 : a 15 ≠ 11 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 11 d7 c26 (by decide +kernel)
  have t4 : a 15 ∈ [0,1,4,5] := remove (a 15) 11 [0,1,4,5,11] t3 b4
  have b5 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b5
  have b6 : a 11 ≠ 3 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0] := remove (a 11) 3 [0,3] d11 b6
  have b7 : a 14 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 2 d10 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,1] := remove (a 14) 2 [0,1,2] d14 b7
  have b8 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 t6 c39 (by decide +kernel)
  have t8 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b8
  have b9 : a 12 ≠ 2 := exclude [0,1] (edge r41) (a 12) (a 14) 2 t7 c41 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,3,4,5] := remove (a 12) 2 [0,1,2,3,4,5] d12 b9
  have b10 : a 12 ≠ 3 := exclude [0,1] (edge r41) (a 12) (a 14) 3 t7 c41 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,4,5] := remove (a 12) 3 [0,1,3,4,5] t9 b10
  have b11 : a 12 ≠ 1 := exclude [0,1] (edge r42) (a 12) (a 28) 1 d28 c42 (by decide +kernel)
  have t11 : a 12 ∈ [0,4,5] := remove (a 12) 1 [0,1,4,5] t10 b11
  have b12 : a 12 ≠ 4 := exclude [0,1] (edge r42) (a 12) (a 28) 4 d28 c42 (by decide +kernel)
  have t12 : a 12 ∈ [0,5] := remove (a 12) 4 [0,4,5] t11 b12
  have b13 : a 28 ≠ 1 := exclude [0,5] (fun u v => edge r42 v u) (a 28) (a 12) 1 t12 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b13
  have b14 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t14 : a 29 ∈ [0,2,3,4,5] := remove (a 29) 1 [0,1,2,3,4,5] d29 b14
  have b15 : a 30 ≠ 1 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 1 t7 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2,3] := remove (a 30) 1 [0,1,2,3] d30 b15
  exact And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,4,5])
    (d31 : a 31 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d30 : a 30 ∈ [0,2,3])
    (d25 : a 25 ∈ [0,1])
    (d29 : a 29 ∈ [0,2,3,4,5])
    (d3 : a 3 ∈ [0,1,2])
    (d7 : a 7 ∈ [0,2])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0,2])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 15 ∈ [0] ∧ a 31 ∈ [0] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0] ∧ a 20 ∈ [0] ∧ a 30 ∈ [0] ∧ a 25 ∈ [0] ∧ a 29 ∈ [0] ∧ a 3 ∈ [0,1] ∧ a 4 ∈ [0,2,3,4,5] := by
  have b0 : a 15 ≠ 1 := exclude [0,1] (edge r47) (a 15) (a 31) 1 d31 c47 (by decide +kernel)
  have t0 : a 15 ∈ [0,4,5] := remove (a 15) 1 [0,1,4,5] d15 b0
  have b1 : a 15 ≠ 4 := exclude [0,1] (edge r47) (a 15) (a 31) 4 d31 c47 (by decide +kernel)
  have t1 : a 15 ∈ [0,5] := remove (a 15) 4 [0,4,5] t0 b1
  have b2 : a 15 ≠ 5 := exclude [0,1] (edge r47) (a 15) (a 31) 5 d31 c47 (by decide +kernel)
  have t2 : a 15 ∈ [0] := remove (a 15) 5 [0,5] t1 b2
  have b3 : a 31 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 1 t2 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b3
  have b4 : a 18 ≠ 1 := exclude [0] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b4
  have b5 : a 19 ≠ 1 := exclude [0] (edge r59) (a 19) (a 27) 1 d27 c59 (by decide +kernel)
  have t5 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b5
  have b6 : a 20 ≠ 1 := exclude [0] (edge r62) (a 20) (a 28) 1 d28 c62 (by decide +kernel)
  have t6 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b6
  have b7 : a 30 ≠ 2 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 2 d22 c66 (by decide +kernel)
  have t7 : a 30 ∈ [0,3] := remove (a 30) 2 [0,2,3] d30 b7
  have b8 : a 30 ≠ 3 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 3 d22 c66 (by decide +kernel)
  have t8 : a 30 ∈ [0] := remove (a 30) 3 [0,3] t7 b8
  have b9 : a 25 ≠ 1 := exclude [0] (edge r71) (a 25) (a 27) 1 d27 c71 (by decide +kernel)
  have t9 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b9
  have b10 : a 29 ≠ 2 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 2 t9 c72 (by decide +kernel)
  have t10 : a 29 ∈ [0,3,4,5] := remove (a 29) 2 [0,2,3,4,5] d29 b10
  have b11 : a 29 ≠ 4 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 4 t9 c72 (by decide +kernel)
  have t11 : a 29 ∈ [0,3,5] := remove (a 29) 4 [0,3,4,5] t10 b11
  have b12 : a 29 ≠ 5 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 5 t9 c72 (by decide +kernel)
  have t12 : a 29 ∈ [0,3] := remove (a 29) 5 [0,3,5] t11 b12
  have b13 : a 29 ≠ 3 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 3 d28 c76 (by decide +kernel)
  have t13 : a 29 ∈ [0] := remove (a 29) 3 [0,3] t12 b13
  have b14 : a 3 ≠ 2 := exclude [0,2] (edge r13) (a 3) (a 7) 2 d7 c13 (by decide +kernel)
  have t14 : a 3 ∈ [0,1] := remove (a 3) 2 [0,1,2] d3 b14
  have b15 : a 4 ≠ 1 := exclude [0,2] (edge r16) (a 4) (a 5) 1 d5 c16 (by decide +kernel)
  have t15 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b15
  exact And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t13 (And.intro t14 (t15)))))))))

theorem chunk3 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,2,3,4,5])
    (d5 : a 5 ∈ [0,2])
    (d12 : a 12 ∈ [0,5])
    (d7 : a 7 ∈ [0,2])
    (d15 : a 15 ∈ [0])
    (d14 : a 14 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d23 : a 23 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d21 : a 21 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d3 : a 3 ∈ [0,1])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 7 ∈ [0] ∧ a 14 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0] ∧ a 23 ∈ [0] ∧ a 21 ∈ [0] ∧ a 3 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 4 ≠ 3 := exclude [0,2] (edge r16) (a 4) (a 5) 3 d5 c16 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,4,5] := remove (a 4) 3 [0,2,3,4,5] d4 b0
  have b1 : a 4 ≠ 4 := exclude [0,2] (edge r16) (a 4) (a 5) 4 d5 c16 (by decide +kernel)
  have t1 : a 4 ∈ [0,2,5] := remove (a 4) 4 [0,2,4,5] t0 b1
  have b2 : a 4 ≠ 5 := exclude [0,2] (edge r16) (a 4) (a 5) 5 d5 c16 (by decide +kernel)
  have t2 : a 4 ∈ [0,2] := remove (a 4) 5 [0,2,5] t1 b2
  have b3 : a 4 ≠ 2 := exclude [0,5] (edge r18) (a 4) (a 12) 2 d12 c18 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 2 [0,2] t2 b3
  have b4 : a 12 ≠ 5 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 5 t3 c18 (by decide +kernel)
  have t4 : a 12 ∈ [0] := remove (a 12) 5 [0,5] d12 b4
  have b5 : a 7 ≠ 2 := exclude [0] (edge r26) (a 7) (a 15) 2 d15 c26 (by decide +kernel)
  have t5 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b5
  have b6 : a 14 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 14) (a 12) 1 t4 c41 (by decide +kernel)
  have t6 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b6
  have b7 : a 16 ≠ 1 := exclude [0] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b7
  have b8 : a 17 ≠ 1 := exclude [0] (edge r54) (a 17) (a 25) 1 d25 c54 (by decide +kernel)
  have t8 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b8
  have b9 : a 23 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 1 d19 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b9
  have b10 : a 21 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 1 d20 c60 (by decide +kernel)
  have t10 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b10
  have b11 : a 3 ≠ 1 := exclude [0] (edge r13) (a 3) (a 7) 1 t5 c13 (by decide +kernel)
  have t11 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b11
  have b12 : a 5 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 2 t3 c16 (by decide +kernel)
  have t12 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b12
  exact And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12)))))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0])
    (start9 : a 9 ∈ [0])
    (start10 : a 10 ∈ [0])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0])
    (start14 : a 14 ∈ [0,1,2])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1])
    (start20 : a 20 ∈ [0,1])
    (start21 : a 21 ∈ [0,1])
    (start22 : a 22 ∈ [0,1])
    (start23 : a 23 ∈ [0,1])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0,1])
    (start26 : a 26 ∈ [0])
    (start27 : a 27 ∈ [0,1])
    (start28 : a 28 ∈ [0,1])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2,3])
    (start31 : a 31 ∈ [0,1])
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
  have group1 := chunk0 a start11 start3 start5 start7 start22 start6 start15 c14 c20 c25 c26
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  have group7 := chunk1 a h6 h4 start24 start8 h2 start9 start14 start10 start27 start12 start28 start29 start13 start30 c26 c31 c32 c36 c39 c41 c42 c44 c46
  rcases group7 with ⟨h8,h9,h10,h11,h12,h13,h14,h15,h16⟩
  have group17 := chunk2 a h8 start31 start18 h5 start19 h12 start20 h14 h16 start25 h15 start3 h4 start4 h3 c13 c16 c47 c56 c59 c62 c66 c71 c72 c76
  rcases group17 with ⟨h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩
  have group28 := chunk3 a h27 h3 h13 h4 h18 h11 start16 h20 start17 h24 start23 h21 start21 h22 h26 c13 c16 c18 c26 c41 c49 c54 c58 c60
  rcases group28 with ⟨h29,h30,h31,h32,h33,h34,h35,h36,h37,h38⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h37) (And.intro (forced (a 4) 0 h29) (And.intro (forced (a 5) 0 h38) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 h31) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 0 start10) (And.intro (forced (a 11) 0 h10) (And.intro (forced (a 12) 0 h30) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 0 h32) (And.intro (forced (a 15) 0 h18) (And.intro (forced (a 16) 0 h33) (And.intro (forced (a 17) 0 h34) (And.intro (forced (a 18) 0 h20) (And.intro (forced (a 19) 0 h21) (And.intro (forced (a 20) 0 h22) (And.intro (forced (a 21) 0 h36) (And.intro (forced (a 22) 0 h5) (And.intro (forced (a 23) 0 h35) (And.intro (forced (a 24) 0 h9) (And.intro (forced (a 25) 0 h24) (And.intro (forced (a 26) 0 start26) (And.intro (forced (a 27) 0 h12) (And.intro (forced (a 28) 0 h14) (And.intro (forced (a 29) 0 h25) (And.intro (forced (a 30) 0 h23) (forced (a 31) 0 h19)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_173
