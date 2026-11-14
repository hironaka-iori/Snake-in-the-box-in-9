import FiniteDomain205
namespace PartitionCover205_172
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[4095]
def r5 : Array Nat := #[7]
def r6 : Array Nat := #[3]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[4095]
def r9 : Array Nat := #[7]
def r10 : Array Nat := #[1]
def r11 : Array Nat := #[1]
def r12 : Array Nat := #[4095]
def r13 : Array Nat := #[1,0,2]
def r14 : Array Nat := #[1,1,1]
def r15 : Array Nat := #[3,3,3]
def r16 : Array Nat := #[1,2]
def r17 : Array Nat := #[1,0]
def r18 : Array Nat := #[1,2]
def r19 : Array Nat := #[63,63]
def r20 : Array Nat := #[1,2]
def r21 : Array Nat := #[1,2]
def r22 : Array Nat := #[63,63]
def r23 : Array Nat := #[1]
def r24 : Array Nat := #[1]
def r25 : Array Nat := #[63]
def r26 : Array Nat := #[1,2]
def r27 : Array Nat := #[63,63]
def r28 : Array Nat := #[1]
def r29 : Array Nat := #[1]
def r30 : Array Nat := #[3]
def r31 : Array Nat := #[233]
def r32 : Array Nat := #[1]
def r33 : Array Nat := #[1]
def r34 : Array Nat := #[1]
def r35 : Array Nat := #[1]
def r36 : Array Nat := #[3]
def r37 : Array Nat := #[3]
def r38 : Array Nat := #[1]
def r39 : Array Nat := #[63]
def r40 : Array Nat := #[1,2]
def r41 : Array Nat := #[1,2]
def r42 : Array Nat := #[33,0]
def r43 : Array Nat := #[1,2]
def r44 : Array Nat := #[5,7]
def r45 : Array Nat := #[1,2]
def r46 : Array Nat := #[63,4032]
def r47 : Array Nat := #[7,56]
def r48 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r49 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r50 : Array Nat := #[63,63,63,63,63,63,63,63,63,63,63,63]
def r51 : Array Nat := #[73,18,260,260,18,73,260,18,160,160,18,260]
def r52 : Array Nat := #[63,63,63,63,63,63,63,63,63,63,63,63]
def r53 : Array Nat := #[63,63,63,63,63,63,63,63,63,63,63,63]
def r54 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r55 : Array Nat := #[63,63,63,63,63,63,63,63,63,63,63,63]
def r56 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r57 : Array Nat := #[1,1,1,1,1,1,2,2,2,2,2,2]
def r58 : Array Nat := #[1,2,4,8,16,32]
def r59 : Array Nat := #[1,2,4,8,16,32]
def r60 : Array Nat := #[1,2,4,8,16,32]
def r61 : Array Nat := #[4095,4095,4095,4095,4095,4095]
def r62 : Array Nat := #[1,2,4,8,16,32]
def r63 : Array Nat := #[1,2,4,8,16,32]
def r64 : Array Nat := #[7,7,7,7,7,7]
def r65 : Array Nat := #[63,63,63,63,63,63,63,63,63,63,63,63]
def r66 : Array Nat := #[1,0,0,0,0,32,0,0,64,2048,0,0]
def r67 : Array Nat := #[9,9,16,16,36,36]
def r68 : Array Nat := #[33,146,76,1,1026,256,32,512,2056]
def r69 : Array Nat := #[1,3,3,1,3,2,0,0,0]
def r70 : Array Nat := #[33,33,33,10,10,10,20,20,20]
def r71 : Array Nat := #[3,0,0,0,0,48,0,0,0,0,0,0]
def r72 : Array Nat := #[1,0,1,0,4,4,1,4,1,4,2,2]
def r73 : Array Nat := #[3,0]
def r74 : Array Nat := #[33,2112]
def r75 : Array Nat := #[1,1,0,0,4,4]
def r76 : Array Nat := #[5,3,6,3,6,5]
def r77 : Array Nat := #[33,10,20,10,20,33]
def r78 : Array Nat := #[61,56,61]
def r79 : Array Nat := #[5,0,0,0,0,5,40,0,0,0,0,40]
theorem chunk0 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1,2])
    (d7 : a 7 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d15 : a 15 ∈ [0,1])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 3 ∈ [0,2] ∧ a 19 ∈ [0,1] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 7 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0,1,2,3,4,5] ∧ a 15 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0,1] (edge r13) (a 3) (a 7) 1 d7 c13 (by decide +kernel)
  have t0 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b0
  have b1 : a 19 ≠ 2 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 2 t0 c15 (by decide +kernel)
  have t1 : a 19 ∈ [0,1,3,4,5] := remove (a 19) 2 [0,1,2,3,4,5] d19 b1
  have b2 : a 19 ≠ 3 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 3 t0 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,4,5] := remove (a 19) 3 [0,1,3,4,5] t1 b2
  have b3 : a 19 ≠ 4 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 4 t0 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,1,5] := remove (a 19) 4 [0,1,4,5] t2 b3
  have b4 : a 19 ≠ 5 := exclude [0,2] (fun u v => edge r15 v u) (a 19) (a 3) 5 t0 c15 (by decide +kernel)
  have t4 : a 19 ∈ [0,1] := remove (a 19) 5 [0,1,5] t3 b4
  have b5 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 d6 c17 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b5
  have b6 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t5 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b6
  have b7 : a 7 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 7) (a 6) 1 d6 c23 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b7
  have b8 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 d6 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b8
  have b9 : a 22 ≠ 6 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 6 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,2,3,4,5,7,8,9,10,11] := remove (a 22) 6 [0,1,2,3,4,5,6,7,8,9,10,11] d22 b9
  have b10 : a 22 ≠ 7 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 7 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,2,3,4,5,8,9,10,11] := remove (a 22) 7 [0,1,2,3,4,5,7,8,9,10,11] t9 b10
  have b11 : a 22 ≠ 8 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 8 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,2,3,4,5,9,10,11] := remove (a 22) 8 [0,1,2,3,4,5,8,9,10,11] t10 b11
  have b12 : a 22 ≠ 9 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 9 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1,2,3,4,5,10,11] := remove (a 22) 9 [0,1,2,3,4,5,9,10,11] t11 b12
  have b13 : a 22 ≠ 10 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 10 d6 c25 (by decide +kernel)
  have t13 : a 22 ∈ [0,1,2,3,4,5,11] := remove (a 22) 10 [0,1,2,3,4,5,10,11] t12 b13
  have b14 : a 22 ≠ 11 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 11 d6 c25 (by decide +kernel)
  have t14 : a 22 ∈ [0,1,2,3,4,5] := remove (a 22) 11 [0,1,2,3,4,5,11] t13 b14
  have b15 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 t7 c26 (by decide +kernel)
  have t15 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t14 (t15)))))))

theorem chunk1 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8])
    (d8 : a 8 ∈ [0])
    (d13 : a 13 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    : a 24 ∈ [0,3,5,6,7] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] := by
  have b0 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,3,4,5,6,7,8] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8] d24 b0
  have b1 : a 24 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,3,4,5,6,7,8] := remove (a 24) 2 [0,2,3,4,5,6,7,8] t0 b1
  have b2 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t2 : a 24 ∈ [0,3,5,6,7,8] := remove (a 24) 4 [0,3,4,5,6,7,8] t1 b2
  have b3 : a 24 ≠ 8 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 8 d8 c31 (by decide +kernel)
  have t3 : a 24 ∈ [0,3,5,6,7] := remove (a 24) 8 [0,3,5,6,7,8] t2 b3
  have b4 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b4
  have b5 : a 25 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 25) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d25 b5
  have b6 : a 25 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t6 : a 25 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 25) 2 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 25 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t7 : a 25 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 25 ≠ 4 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 4 d9 c34 (by decide +kernel)
  have t8 : a 25 ∈ [0,5,6,7,8,9,10,11] := remove (a 25) 4 [0,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 25 ≠ 5 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 5 d9 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0,6,7,8,9,10,11] := remove (a 25) 5 [0,5,6,7,8,9,10,11] t8 b9
  have b10 : a 25 ≠ 6 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 6 d9 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0,7,8,9,10,11] := remove (a 25) 6 [0,6,7,8,9,10,11] t9 b10
  have b11 : a 25 ≠ 7 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 7 d9 c34 (by decide +kernel)
  have t11 : a 25 ∈ [0,8,9,10,11] := remove (a 25) 7 [0,7,8,9,10,11] t10 b11
  have b12 : a 25 ≠ 8 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t12 : a 25 ∈ [0,9,10,11] := remove (a 25) 8 [0,8,9,10,11] t11 b12
  have b13 : a 25 ≠ 9 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 9 d9 c34 (by decide +kernel)
  have t13 : a 25 ∈ [0,10,11] := remove (a 25) 9 [0,9,10,11] t12 b13
  have b14 : a 25 ≠ 10 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 10 d9 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0,11] := remove (a 25) 10 [0,10,11] t13 b14
  have b15 : a 25 ≠ 11 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 11 d9 c34 (by decide +kernel)
  have t15 : a 25 ∈ [0] := remove (a 25) 11 [0,11] t14 b15
  exact And.intro t3 (And.intro t4 (t15))

theorem chunk2 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1,2])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d24 : a 24 ∈ [0,3,5,6,7])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    : a 28 ∈ [0,5] ∧ a 29 ∈ [0,2] ∧ a 30 ∈ [0,1,2,3,4,5] ∧ a 31 ∈ [0,1,2] ∧ a 16 ∈ [0,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,3,4,5] := remove (a 28) 1 [0,1,2,3,4,5] d28 b0
  have b1 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,3,4,5] := remove (a 28) 2 [0,2,3,4,5] t0 b1
  have b2 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,4,5] := remove (a 28) 3 [0,3,4,5] t1 b2
  have b3 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,5] := remove (a 28) 4 [0,4,5] t2 b3
  have b4 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,2] := remove (a 29) 1 [0,1,2] d29 b4
  have b5 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,2,3,4,5,7,8,9,10,11] := remove (a 30) 6 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b5
  have b6 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,2,3,4,5,8,9,10,11] := remove (a 30) 7 [0,1,2,3,4,5,7,8,9,10,11] t5 b6
  have b7 : a 30 ≠ 8 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,2,3,4,5,9,10,11] := remove (a 30) 8 [0,1,2,3,4,5,8,9,10,11] t6 b7
  have b8 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,2,3,4,5,10,11] := remove (a 30) 9 [0,1,2,3,4,5,9,10,11] t7 b8
  have b9 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,2,3,4,5,11] := remove (a 30) 10 [0,1,2,3,4,5,10,11] t8 b9
  have b10 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,1,2,3,4,5] := remove (a 30) 11 [0,1,2,3,4,5,11] t9 b10
  have b11 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1,2,4,5] := remove (a 31) 3 [0,1,2,3,4,5] d31 b11
  have b12 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,2,5] := remove (a 31) 4 [0,1,2,4,5] t11 b12
  have b13 : a 31 ≠ 5 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 5 d15 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,2] := remove (a 31) 5 [0,1,2,5] t12 b13
  have b14 : a 16 ≠ 1 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 1 d24 c51 (by decide +kernel)
  have t14 : a 16 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 16) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d16 b14
  have b15 : a 16 ≠ 2 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 2 d24 c51 (by decide +kernel)
  have t15 : a 16 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 16) 2 [0,2,3,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t4 (And.intro t10 (And.intro t13 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d16 : a 16 ∈ [0,3,4,5,6,7,8,9,10,11])
    (d24 : a 24 ∈ [0,3,5,6,7])
    (d17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d25 : a 25 ∈ [0])
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    : a 16 ∈ [0,5,8,9] ∧ a 17 ∈ [0,11] := by
  have b0 : a 16 ≠ 3 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 3 d24 c51 (by decide +kernel)
  have t0 : a 16 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 16) 3 [0,3,4,5,6,7,8,9,10,11] d16 b0
  have b1 : a 16 ≠ 4 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 4 d24 c51 (by decide +kernel)
  have t1 : a 16 ∈ [0,5,6,7,8,9,10,11] := remove (a 16) 4 [0,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 16 ≠ 6 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 6 d24 c51 (by decide +kernel)
  have t2 : a 16 ∈ [0,5,7,8,9,10,11] := remove (a 16) 6 [0,5,6,7,8,9,10,11] t1 b2
  have b3 : a 16 ≠ 7 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 7 d24 c51 (by decide +kernel)
  have t3 : a 16 ∈ [0,5,8,9,10,11] := remove (a 16) 7 [0,5,7,8,9,10,11] t2 b3
  have b4 : a 16 ≠ 10 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 10 d24 c51 (by decide +kernel)
  have t4 : a 16 ∈ [0,5,8,9,11] := remove (a 16) 10 [0,5,8,9,10,11] t3 b4
  have b5 : a 16 ≠ 11 := exclude [0,3,5,6,7] (edge r51) (a 16) (a 24) 11 d24 c51 (by decide +kernel)
  have t5 : a 16 ∈ [0,5,8,9] := remove (a 16) 11 [0,5,8,9,11] t4 b5
  have b6 : a 17 ≠ 1 := exclude [0] (edge r54) (a 17) (a 25) 1 d25 c54 (by decide +kernel)
  have t6 : a 17 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 17) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d17 b6
  have b7 : a 17 ≠ 2 := exclude [0] (edge r54) (a 17) (a 25) 2 d25 c54 (by decide +kernel)
  have t7 : a 17 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 17) 2 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 17 ≠ 3 := exclude [0] (edge r54) (a 17) (a 25) 3 d25 c54 (by decide +kernel)
  have t8 : a 17 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 17) 3 [0,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 17 ≠ 4 := exclude [0] (edge r54) (a 17) (a 25) 4 d25 c54 (by decide +kernel)
  have t9 : a 17 ∈ [0,5,6,7,8,9,10,11] := remove (a 17) 4 [0,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 17 ≠ 5 := exclude [0] (edge r54) (a 17) (a 25) 5 d25 c54 (by decide +kernel)
  have t10 : a 17 ∈ [0,6,7,8,9,10,11] := remove (a 17) 5 [0,5,6,7,8,9,10,11] t9 b10
  have b11 : a 17 ≠ 6 := exclude [0] (edge r54) (a 17) (a 25) 6 d25 c54 (by decide +kernel)
  have t11 : a 17 ∈ [0,7,8,9,10,11] := remove (a 17) 6 [0,6,7,8,9,10,11] t10 b11
  have b12 : a 17 ≠ 7 := exclude [0] (edge r54) (a 17) (a 25) 7 d25 c54 (by decide +kernel)
  have t12 : a 17 ∈ [0,8,9,10,11] := remove (a 17) 7 [0,7,8,9,10,11] t11 b12
  have b13 : a 17 ≠ 8 := exclude [0] (edge r54) (a 17) (a 25) 8 d25 c54 (by decide +kernel)
  have t13 : a 17 ∈ [0,9,10,11] := remove (a 17) 8 [0,8,9,10,11] t12 b13
  have b14 : a 17 ≠ 9 := exclude [0] (edge r54) (a 17) (a 25) 9 d25 c54 (by decide +kernel)
  have t14 : a 17 ∈ [0,10,11] := remove (a 17) 9 [0,9,10,11] t13 b14
  have b15 : a 17 ≠ 10 := exclude [0] (edge r54) (a 17) (a 25) 10 d25 c54 (by decide +kernel)
  have t15 : a 17 ∈ [0,11] := remove (a 17) 10 [0,10,11] t14 b15
  exact And.intro t5 (t15)

theorem chunk4 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,11])
    (d25 : a 25 ∈ [0])
    (d18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d26 : a 26 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2,3,4,5])
    (c54 : edge r54 (a 17) (a 25)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 17 ∈ [0] ∧ a 18 ∈ [0,1,2,3,4,5] ∧ a 26 ∈ [0] ∧ a 23 ∈ [0,1] ∧ a 27 ∈ [0,1] := by
  have b0 : a 17 ≠ 11 := exclude [0] (edge r54) (a 17) (a 25) 11 d25 c54 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 11 [0,11] d17 b0
  have b1 : a 18 ≠ 6 := exclude [0,1,2,3,4,5] (edge r56) (a 18) (a 22) 6 d22 c56 (by decide +kernel)
  have t1 : a 18 ∈ [0,1,2,3,4,5,7,8,9,10,11] := remove (a 18) 6 [0,1,2,3,4,5,6,7,8,9,10,11] d18 b1
  have b2 : a 18 ≠ 7 := exclude [0,1,2,3,4,5] (edge r56) (a 18) (a 22) 7 d22 c56 (by decide +kernel)
  have t2 : a 18 ∈ [0,1,2,3,4,5,8,9,10,11] := remove (a 18) 7 [0,1,2,3,4,5,7,8,9,10,11] t1 b2
  have b3 : a 18 ≠ 8 := exclude [0,1,2,3,4,5] (edge r56) (a 18) (a 22) 8 d22 c56 (by decide +kernel)
  have t3 : a 18 ∈ [0,1,2,3,4,5,9,10,11] := remove (a 18) 8 [0,1,2,3,4,5,8,9,10,11] t2 b3
  have b4 : a 18 ≠ 9 := exclude [0,1,2,3,4,5] (edge r56) (a 18) (a 22) 9 d22 c56 (by decide +kernel)
  have t4 : a 18 ∈ [0,1,2,3,4,5,10,11] := remove (a 18) 9 [0,1,2,3,4,5,9,10,11] t3 b4
  have b5 : a 18 ≠ 10 := exclude [0,1,2,3,4,5] (edge r56) (a 18) (a 22) 10 d22 c56 (by decide +kernel)
  have t5 : a 18 ∈ [0,1,2,3,4,5,11] := remove (a 18) 10 [0,1,2,3,4,5,10,11] t4 b5
  have b6 : a 18 ≠ 11 := exclude [0,1,2,3,4,5] (edge r56) (a 18) (a 22) 11 d22 c56 (by decide +kernel)
  have t6 : a 18 ∈ [0,1,2,3,4,5] := remove (a 18) 11 [0,1,2,3,4,5,11] t5 b6
  have b7 : a 26 ≠ 1 := exclude [0,1,2,3,4,5] (fun u v => edge r57 v u) (a 26) (a 18) 1 t6 c57 (by decide +kernel)
  have t7 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b7
  have b8 : a 23 ≠ 2 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t8 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] d23 b8
  have b9 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t9 : a 23 ∈ [0,1,4,5] := remove (a 23) 3 [0,1,3,4,5] t8 b9
  have b10 : a 23 ≠ 4 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 4 d19 c58 (by decide +kernel)
  have t10 : a 23 ∈ [0,1,5] := remove (a 23) 4 [0,1,4,5] t9 b10
  have b11 : a 23 ≠ 5 := exclude [0,1] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t11 : a 23 ∈ [0,1] := remove (a 23) 5 [0,1,5] t10 b11
  have b12 : a 27 ≠ 2 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 2 d19 c59 (by decide +kernel)
  have t12 : a 27 ∈ [0,1,3,4,5] := remove (a 27) 2 [0,1,2,3,4,5] d27 b12
  have b13 : a 27 ≠ 3 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 3 d19 c59 (by decide +kernel)
  have t13 : a 27 ∈ [0,1,4,5] := remove (a 27) 3 [0,1,3,4,5] t12 b13
  have b14 : a 27 ≠ 4 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 4 d19 c59 (by decide +kernel)
  have t14 : a 27 ∈ [0,1,5] := remove (a 27) 4 [0,1,4,5] t13 b14
  have b15 : a 27 ≠ 5 := exclude [0,1] (fun u v => edge r59 v u) (a 27) (a 19) 5 d19 c59 (by decide +kernel)
  have t15 : a 27 ∈ [0,1] := remove (a 27) 5 [0,1,5] t14 b15
  exact And.intro t0 (And.intro t6 (And.intro t7 (And.intro t11 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d28 : a 28 ∈ [0,5])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d30 : a 30 ∈ [0,1,2,3,4,5])
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 20 ∈ [0,5] ∧ a 21 ∈ [0,1] ∧ a 22 ∈ [0,5] ∧ a 30 ∈ [0,5] := by
  have b0 : a 20 ≠ 1 := exclude [0,5] (edge r62) (a 20) (a 28) 1 d28 c62 (by decide +kernel)
  have t0 : a 20 ∈ [0,2,3,4,5] := remove (a 20) 1 [0,1,2,3,4,5] d20 b0
  have b1 : a 20 ≠ 2 := exclude [0,5] (edge r62) (a 20) (a 28) 2 d28 c62 (by decide +kernel)
  have t1 : a 20 ∈ [0,3,4,5] := remove (a 20) 2 [0,2,3,4,5] t0 b1
  have b2 : a 20 ≠ 3 := exclude [0,5] (edge r62) (a 20) (a 28) 3 d28 c62 (by decide +kernel)
  have t2 : a 20 ∈ [0,4,5] := remove (a 20) 3 [0,3,4,5] t1 b2
  have b3 : a 20 ≠ 4 := exclude [0,5] (edge r62) (a 20) (a 28) 4 d28 c62 (by decide +kernel)
  have t3 : a 20 ∈ [0,5] := remove (a 20) 4 [0,4,5] t2 b3
  have b4 : a 21 ≠ 2 := exclude [0,1] (edge r63) (a 21) (a 23) 2 d23 c63 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b4
  have b5 : a 21 ≠ 3 := exclude [0,1] (edge r63) (a 21) (a 23) 3 d23 c63 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] t4 b5
  have b6 : a 21 ≠ 4 := exclude [0,1] (edge r63) (a 21) (a 23) 4 d23 c63 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t5 b6
  have b7 : a 21 ≠ 5 := exclude [0,1] (edge r63) (a 21) (a 23) 5 d23 c63 (by decide +kernel)
  have t7 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t6 b7
  have b8 : a 22 ≠ 1 := exclude [0,1,2,3,4,5] (edge r66) (a 22) (a 30) 1 d30 c66 (by decide +kernel)
  have t8 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b8
  have b9 : a 22 ≠ 2 := exclude [0,1,2,3,4,5] (edge r66) (a 22) (a 30) 2 d30 c66 (by decide +kernel)
  have t9 : a 22 ∈ [0,3,4,5] := remove (a 22) 2 [0,2,3,4,5] t8 b9
  have b10 : a 22 ≠ 3 := exclude [0,1,2,3,4,5] (edge r66) (a 22) (a 30) 3 d30 c66 (by decide +kernel)
  have t10 : a 22 ∈ [0,4,5] := remove (a 22) 3 [0,3,4,5] t9 b10
  have b11 : a 22 ≠ 4 := exclude [0,1,2,3,4,5] (edge r66) (a 22) (a 30) 4 d30 c66 (by decide +kernel)
  have t11 : a 22 ∈ [0,5] := remove (a 22) 4 [0,4,5] t10 b11
  have b12 : a 30 ≠ 1 := exclude [0,5] (fun u v => edge r66 v u) (a 30) (a 22) 1 t11 c66 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,3,4,5] := remove (a 30) 1 [0,1,2,3,4,5] d30 b12
  have b13 : a 30 ≠ 2 := exclude [0,5] (fun u v => edge r66 v u) (a 30) (a 22) 2 t11 c66 (by decide +kernel)
  have t13 : a 30 ∈ [0,3,4,5] := remove (a 30) 2 [0,2,3,4,5] t12 b13
  have b14 : a 30 ≠ 3 := exclude [0,5] (fun u v => edge r66 v u) (a 30) (a 22) 3 t11 c66 (by decide +kernel)
  have t14 : a 30 ∈ [0,4,5] := remove (a 30) 3 [0,3,4,5] t13 b14
  have b15 : a 30 ≠ 4 := exclude [0,5] (fun u v => edge r66 v u) (a 30) (a 22) 4 t11 c66 (by decide +kernel)
  have t15 : a 30 ∈ [0,5] := remove (a 30) 4 [0,4,5] t14 b15
  exact And.intro t3 (And.intro t7 (And.intro t11 (t15)))

theorem chunk6 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2])
    (d23 : a 23 ∈ [0,1])
    (d24 : a 24 ∈ [0,3,5,6,7])
    (d25 : a 25 ∈ [0])
    (d28 : a 28 ∈ [0,5])
    (d29 : a 29 ∈ [0,2])
    (d3 : a 3 ∈ [0,2])
    (d7 : a 7 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d16 : a 16 ∈ [0,5,8,9])
    (d17 : a 17 ∈ [0])
    (d18 : a 18 ∈ [0,1,2,3,4,5])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 31 ∈ [0] ∧ a 24 ∈ [0] ∧ a 29 ∈ [0] ∧ a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0,5] := by
  have b0 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 1 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,2] := remove (a 31) 1 [0,1,2] d31 b0
  have b1 : a 31 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 2 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0] := remove (a 31) 2 [0,2] t0 b1
  have b2 : a 24 ≠ 5 := exclude [0] (edge r68) (a 24) (a 25) 5 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0,3,6,7] := remove (a 24) 5 [0,3,5,6,7] d24 b2
  have b3 : a 24 ≠ 6 := exclude [0] (edge r68) (a 24) (a 25) 6 d25 c68 (by decide +kernel)
  have t3 : a 24 ∈ [0,3,7] := remove (a 24) 6 [0,3,6,7] t2 b3
  have b4 : a 24 ≠ 7 := exclude [0] (edge r68) (a 24) (a 25) 7 d25 c68 (by decide +kernel)
  have t4 : a 24 ∈ [0,3] := remove (a 24) 7 [0,3,7] t3 b4
  have b5 : a 24 ≠ 3 := exclude [0,5] (edge r70) (a 24) (a 28) 3 d28 c70 (by decide +kernel)
  have t5 : a 24 ∈ [0] := remove (a 24) 3 [0,3] t4 b5
  have b6 : a 29 ≠ 2 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 2 d25 c72 (by decide +kernel)
  have t6 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b6
  have b7 : a 3 ≠ 2 := exclude [0] (edge r13) (a 3) (a 7) 2 d7 c13 (by decide +kernel)
  have t7 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b7
  have b8 : a 5 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t8 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b8
  have b9 : a 16 ≠ 5 := exclude [0] (edge r48) (a 16) (a 17) 5 d17 c48 (by decide +kernel)
  have t9 : a 16 ∈ [0,8,9] := remove (a 16) 5 [0,5,8,9] d16 b9
  have b10 : a 16 ≠ 8 := exclude [0] (edge r48) (a 16) (a 17) 8 d17 c48 (by decide +kernel)
  have t10 : a 16 ∈ [0,9] := remove (a 16) 8 [0,8,9] t9 b10
  have b11 : a 16 ≠ 9 := exclude [0] (edge r48) (a 16) (a 17) 9 d17 c48 (by decide +kernel)
  have t11 : a 16 ∈ [0] := remove (a 16) 9 [0,9] t10 b11
  have b12 : a 18 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 1 t11 c49 (by decide +kernel)
  have t12 : a 18 ∈ [0,2,3,4,5] := remove (a 18) 1 [0,1,2,3,4,5] d18 b12
  have b13 : a 18 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 2 t11 c49 (by decide +kernel)
  have t13 : a 18 ∈ [0,3,4,5] := remove (a 18) 2 [0,2,3,4,5] t12 b13
  have b14 : a 18 ≠ 3 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 3 t11 c49 (by decide +kernel)
  have t14 : a 18 ∈ [0,4,5] := remove (a 18) 3 [0,3,4,5] t13 b14
  have b15 : a 18 ≠ 4 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 4 t11 c49 (by decide +kernel)
  have t15 : a 18 ∈ [0,5] := remove (a 18) 4 [0,4,5] t14 b15
  exact And.intro t1 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t11 (t15))))))

theorem chunk7 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,5])
    (d16 : a 16 ∈ [0])
    (d22 : a 22 ∈ [0,5])
    (d20 : a 20 ∈ [0,5])
    (d21 : a 21 ∈ [0,1])
    (d28 : a 28 ∈ [0,5])
    (d23 : a 23 ∈ [0,1])
    (d30 : a 30 ∈ [0,5])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (c49 : edge r49 (a 16) (a 18)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 18 ∈ [0] ∧ a 22 ∈ [0] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0] ∧ a 28 ∈ [0] ∧ a 23 ∈ [0] ∧ a 30 ∈ [0] ∧ a 19 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 18 ≠ 5 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 5 d16 c49 (by decide +kernel)
  have t0 : a 18 ∈ [0] := remove (a 18) 5 [0,5] d18 b0
  have b1 : a 22 ≠ 5 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 5 t0 c56 (by decide +kernel)
  have t1 : a 22 ∈ [0] := remove (a 22) 5 [0,5] d22 b1
  have b2 : a 20 ≠ 5 := exclude [0,1] (edge r60) (a 20) (a 21) 5 d21 c60 (by decide +kernel)
  have t2 : a 20 ∈ [0] := remove (a 20) 5 [0,5] d20 b2
  have b3 : a 21 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 1 t2 c60 (by decide +kernel)
  have t3 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b3
  have b4 : a 28 ≠ 5 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 5 t2 c62 (by decide +kernel)
  have t4 : a 28 ∈ [0] := remove (a 28) 5 [0,5] d28 b4
  have b5 : a 23 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 1 t3 c63 (by decide +kernel)
  have t5 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b5
  have b6 : a 30 ≠ 5 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 5 t1 c66 (by decide +kernel)
  have t6 : a 30 ∈ [0] := remove (a 30) 5 [0,5] d30 b6
  have b7 : a 19 ≠ 1 := exclude [0] (edge r58) (a 19) (a 23) 1 t5 c58 (by decide +kernel)
  have t7 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b7
  have b8 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 t7 c59 (by decide +kernel)
  have t8 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0])
    (start9 : a 9 ∈ [0])
    (start10 : a 10 ∈ [0])
    (start11 : a 11 ∈ [0])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1])
    (start14 : a 14 ∈ [0,1])
    (start15 : a 15 ∈ [0,1])
    (start16 : a 16 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start17 : a 17 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start18 : a 18 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start19 : a 19 ∈ [0,1,2,3,4,5])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start23 : a 23 ∈ [0,1,2,3,4,5])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8])
    (start25 : a 25 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start26 : a 26 ∈ [0,1])
    (start27 : a 27 ∈ [0,1,2,3,4,5])
    (start28 : a 28 ∈ [0,1,2,3,4,5])
    (start29 : a 29 ∈ [0,1,2])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start31 : a 31 ∈ [0,1,2,3,4,5])
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
  have group1 := chunk0 a start3 start7 start19 start4 start6 start12 start14 start22 start15 c13 c15 c17 c18 c23 c24 c25 c26
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8,h9⟩
  have group10 := chunk1 a start24 start8 start13 start9 start25 c31 c33 c34
  rcases group10 with ⟨h11,h12,h13⟩
  have group14 := chunk2 a start28 h5 start29 h12 start30 h7 start31 h9 start16 h11 c42 c44 c46 c47 c51
  rcases group14 with ⟨h15,h16,h17,h18,h19⟩
  have group20 := chunk3 a h19 h11 start17 h13 c51 c54
  rcases group20 with ⟨h21,h22⟩
  have group23 := chunk4 a h22 h13 start18 h8 start26 start23 h3 start27 c54 c56 c57 c58 c59
  rcases group23 with ⟨h24,h25,h26,h27,h28⟩
  have group29 := chunk5 a start20 h15 start21 h27 h8 h17 c62 c63 c66
  rcases group29 with ⟨h30,h31,h32,h33⟩
  have group34 := chunk6 a h18 h27 h11 h13 h15 h16 h2 h6 start5 h4 h21 h24 h25 c13 c16 c48 c49 c67 c68 c70 c72
  rcases group34 with ⟨h35,h36,h37,h38,h39,h40,h41⟩
  have group42 := chunk7 a h41 h40 h32 h30 h31 h15 h27 h33 h3 h28 c49 c56 c58 c59 c60 c62 c63 c66
  rcases group42 with ⟨h43,h44,h45,h46,h47,h48,h49,h50,h51⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h38) (And.intro (forced (a 4) 0 h4) (And.intro (forced (a 5) 0 h39) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 h6) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 0 start10) (And.intro (forced (a 11) 0 start11) (And.intro (forced (a 12) 0 h5) (And.intro (forced (a 13) 0 h12) (And.intro (forced (a 14) 0 h7) (And.intro (forced (a 15) 0 h9) (And.intro (forced (a 16) 0 h40) (And.intro (forced (a 17) 0 h24) (And.intro (forced (a 18) 0 h43) (And.intro (forced (a 19) 0 h50) (And.intro (forced (a 20) 0 h45) (And.intro (forced (a 21) 0 h46) (And.intro (forced (a 22) 0 h44) (And.intro (forced (a 23) 0 h48) (And.intro (forced (a 24) 0 h36) (And.intro (forced (a 25) 0 h13) (And.intro (forced (a 26) 0 h26) (And.intro (forced (a 27) 0 h51) (And.intro (forced (a 28) 0 h47) (And.intro (forced (a 29) 0 h37) (And.intro (forced (a 30) 0 h49) (forced (a 31) 0 h35)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_172
