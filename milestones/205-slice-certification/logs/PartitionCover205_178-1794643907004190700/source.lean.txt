import FiniteDomain205
namespace PartitionCover205_178
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[4095]
def r4 : Array Nat := #[15]
def r5 : Array Nat := #[3]
def r6 : Array Nat := #[1]
def r7 : Array Nat := #[4095]
def r8 : Array Nat := #[15]
def r9 : Array Nat := #[3]
def r10 : Array Nat := #[3]
def r11 : Array Nat := #[63]
def r12 : Array Nat := #[3]
def r13 : Array Nat := #[1,1]
def r14 : Array Nat := #[3,0]
def r15 : Array Nat := #[15,0]
def r16 : Array Nat := #[1]
def r17 : Array Nat := #[1]
def r18 : Array Nat := #[3327]
def r19 : Array Nat := #[1]
def r20 : Array Nat := #[1]
def r21 : Array Nat := #[195]
def r22 : Array Nat := #[7]
def r23 : Array Nat := #[1,1]
def r24 : Array Nat := #[1,2]
def r25 : Array Nat := #[1,2]
def r26 : Array Nat := #[7]
def r27 : Array Nat := #[63]
def r28 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r29 : Array Nat := #[1,1,2,2,4,4,8,8,16,16,32,32]
def r30 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r31 : Array Nat := #[63,63,63,63,63,63,63,63,63,63,63,63]
def r32 : Array Nat := #[1,32,0,0,0,0,2,8,0,0,0,0]
def r33 : Array Nat := #[9,9,9,9,9,9,80,80,80,80,80,80]
def r34 : Array Nat := #[63,63,63,63,63,63,63,63,63,63,63,63]
def r35 : Array Nat := #[33,0,0,10,0,0]
def r36 : Array Nat := #[1,1,1,2,2,2]
def r37 : Array Nat := #[3,0,0,12,0,0]
def r38 : Array Nat := #[1,1,2,2,4,4]
def r39 : Array Nat := #[1,2,4,2,4,1]
def r40 : Array Nat := #[9,9,8,8,1,1,80,80,16,16,64,64]
def r41 : Array Nat := #[1,1,0,0,1,1,2,2,0,0,2,2]
def r42 : Array Nat := #[73,73,130,130,36,36,73,73,272,272,36,36]
def r43 : Array Nat := #[1,2,0,4,2,0,1,4,0]
def r44 : Array Nat := #[17,17,17,10,10,10,36,36,36]
def r45 : Array Nat := #[1,1]
def r46 : Array Nat := #[5,80]
def r47 : Array Nat := #[3,6,5]
def r48 : Array Nat := #[1,2,4,8]
def r49 : Array Nat := #[1,1,2,2]
def r50 : Array Nat := #[1,0,2,0]
def r51 : Array Nat := #[63,63,63,63]
def r52 : Array Nat := #[1,2,4,8]
def r53 : Array Nat := #[1,1,4,4]
def r54 : Array Nat := #[63,63,63,63]
def r55 : Array Nat := #[3,12]
def r56 : Array Nat := #[1,2]
def r57 : Array Nat := #[3,12]
def r58 : Array Nat := #[1,2,16,32]
def r59 : Array Nat := #[1,1,2,2]
def r60 : Array Nat := #[1,4]
def r61 : Array Nat := #[1,2]
def r62 : Array Nat := #[1,8]
def r63 : Array Nat := #[3,12,48]
def r64 : Array Nat := #[27,53,46]
def r65 : Array Nat := #[3,48]
def r66 : Array Nat := #[1375,1525]
def r67 : Array Nat := #[1,1,4,4,2,2]
def r68 : Array Nat := #[1,2,4,8,16,32]
def r69 : Array Nat := #[1,2,4,8,16,32]
def r70 : Array Nat := #[7,7,56,56,448,448]
def r71 : Array Nat := #[1,1,2,2,4,4]
def r72 : Array Nat := #[1,2,4,8,16,32]
def r73 : Array Nat := #[1,1,2,2,4,4]
def r74 : Array Nat := #[3,12,48,192,768,3072]
def r75 : Array Nat := #[1,2,4]
def r76 : Array Nat := #[3,2,1,12,8,4,48,32,16]
def r77 : Array Nat := #[4085,240,3840,3935,15,3840,1535,240,15]
def r78 : Array Nat := #[5,3,6,3,5,6]
def r79 : Array Nat := #[1,1,1,1,2,2,2,2,4,4,4,4]
theorem chunk0 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d20 : a 20 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d5 : a 5 ∈ [0])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    : a 3 ∈ [0] ∧ a 11 ∈ [0,1] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0,1,2,3,4,5,6,7,10,11] ∧ a 20 ∈ [0] ∧ a 13 ∈ [0,1,6,7] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0,1,2,3,4,5] (edge r14) (a 3) (a 11) 1 d11 c14 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 t0 c14 (by decide +kernel)
  have t1 : a 11 ∈ [0,1,3,4,5] := remove (a 11) 2 [0,1,2,3,4,5] d11 b1
  have b2 : a 11 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 3 t0 c14 (by decide +kernel)
  have t2 : a 11 ∈ [0,1,4,5] := remove (a 11) 3 [0,1,3,4,5] t1 b2
  have b3 : a 11 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 4 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0,1,5] := remove (a 11) 4 [0,1,4,5] t2 b3
  have b4 : a 11 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 5 t0 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0,1] := remove (a 11) 5 [0,1,5] t3 b4
  have b5 : a 6 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 1 d4 c17 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b5
  have b6 : a 12 ≠ 8 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 8 d4 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,1,2,3,4,5,6,7,9,10,11] := remove (a 12) 8 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b6
  have b7 : a 12 ≠ 9 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 9 d4 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,2,3,4,5,6,7,10,11] := remove (a 12) 9 [0,1,2,3,4,5,6,7,9,10,11] t6 b7
  have b8 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b8
  have b9 : a 13 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 2 d5 c21 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,3,4,5,6,7,8] := remove (a 13) 2 [0,1,2,3,4,5,6,7,8] d13 b9
  have b10 : a 13 ≠ 3 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 3 d5 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,4,5,6,7,8] := remove (a 13) 3 [0,1,3,4,5,6,7,8] t9 b10
  have b11 : a 13 ≠ 4 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 4 d5 c21 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,5,6,7,8] := remove (a 13) 4 [0,1,4,5,6,7,8] t10 b11
  have b12 : a 13 ≠ 5 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 5 d5 c21 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,6,7,8] := remove (a 13) 5 [0,1,5,6,7,8] t11 b12
  have b13 : a 13 ≠ 8 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 8 d5 c21 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,6,7] := remove (a 13) 8 [0,1,6,7,8] t12 b13
  have b14 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 t5 c24 (by decide +kernel)
  have t14 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b14
  have b15 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 t5 c25 (by decide +kernel)
  have t15 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t13 (And.intro t14 (t15)))))))

theorem chunk1 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,10,11])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d11 : a 11 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,6,7])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    : a 8 ∈ [0,1,2,3,4,5,6,7,10,11] ∧ a 9 ∈ [0,6] ∧ a 13 ∈ [0,6] ∧ a 10 ∈ [0,3,4,5] := by
  have b0 : a 8 ≠ 8 := exclude [0,1,2,3,4,5,6,7,10,11] (edge r30) (a 8) (a 12) 8 d12 c30 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,2,3,4,5,6,7,9,10,11] := remove (a 8) 8 [0,1,2,3,4,5,6,7,8,9,10,11] d8 b0
  have b1 : a 8 ≠ 9 := exclude [0,1,2,3,4,5,6,7,10,11] (edge r30) (a 8) (a 12) 9 d12 c30 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,2,3,4,5,6,7,10,11] := remove (a 8) 9 [0,1,2,3,4,5,6,7,9,10,11] t0 b1
  have b2 : a 9 ≠ 1 := exclude [0,1] (edge r32) (a 9) (a 11) 1 d11 c32 (by decide +kernel)
  have t2 : a 9 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 9) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d9 b2
  have b3 : a 9 ≠ 2 := exclude [0,1] (edge r32) (a 9) (a 11) 2 d11 c32 (by decide +kernel)
  have t3 : a 9 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 9) 2 [0,2,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 9 ≠ 3 := exclude [0,1] (edge r32) (a 9) (a 11) 3 d11 c32 (by decide +kernel)
  have t4 : a 9 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 9) 3 [0,3,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 9 ≠ 4 := exclude [0,1] (edge r32) (a 9) (a 11) 4 d11 c32 (by decide +kernel)
  have t5 : a 9 ∈ [0,5,6,7,8,9,10,11] := remove (a 9) 4 [0,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 9 ≠ 5 := exclude [0,1] (edge r32) (a 9) (a 11) 5 d11 c32 (by decide +kernel)
  have t6 : a 9 ∈ [0,6,7,8,9,10,11] := remove (a 9) 5 [0,5,6,7,8,9,10,11] t5 b6
  have b7 : a 9 ≠ 7 := exclude [0,1] (edge r32) (a 9) (a 11) 7 d11 c32 (by decide +kernel)
  have t7 : a 9 ∈ [0,6,8,9,10,11] := remove (a 9) 7 [0,6,7,8,9,10,11] t6 b7
  have b8 : a 9 ≠ 8 := exclude [0,1] (edge r32) (a 9) (a 11) 8 d11 c32 (by decide +kernel)
  have t8 : a 9 ∈ [0,6,9,10,11] := remove (a 9) 8 [0,6,8,9,10,11] t7 b8
  have b9 : a 9 ≠ 9 := exclude [0,1] (edge r32) (a 9) (a 11) 9 d11 c32 (by decide +kernel)
  have t9 : a 9 ∈ [0,6,10,11] := remove (a 9) 9 [0,6,9,10,11] t8 b9
  have b10 : a 9 ≠ 10 := exclude [0,1] (edge r32) (a 9) (a 11) 10 d11 c32 (by decide +kernel)
  have t10 : a 9 ∈ [0,6,11] := remove (a 9) 10 [0,6,10,11] t9 b10
  have b11 : a 9 ≠ 11 := exclude [0,1] (edge r32) (a 9) (a 11) 11 d11 c32 (by decide +kernel)
  have t11 : a 9 ∈ [0,6] := remove (a 9) 11 [0,6,11] t10 b11
  have b12 : a 13 ≠ 1 := exclude [0,6] (fun u v => edge r33 v u) (a 13) (a 9) 1 t11 c33 (by decide +kernel)
  have t12 : a 13 ∈ [0,6,7] := remove (a 13) 1 [0,1,6,7] d13 b12
  have b13 : a 13 ≠ 7 := exclude [0,6] (fun u v => edge r33 v u) (a 13) (a 9) 7 t11 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0,6] := remove (a 13) 7 [0,6,7] t12 b13
  have b14 : a 10 ≠ 1 := exclude [0,1] (edge r35) (a 10) (a 11) 1 d11 c35 (by decide +kernel)
  have t14 : a 10 ∈ [0,2,3,4,5] := remove (a 10) 1 [0,1,2,3,4,5] d10 b14
  have b15 : a 10 ≠ 2 := exclude [0,1] (edge r35) (a 10) (a 11) 2 d11 c35 (by decide +kernel)
  have t15 : a 10 ∈ [0,3,4,5] := remove (a 10) 2 [0,2,3,4,5] t14 b15
  exact And.intro t1 (And.intro t11 (And.intro t13 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,3,4,5])
    (d11 : a 11 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1,2])
    (d27 : a 27 ∈ [0,1,2])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,10,11])
    (d13 : a 13 ∈ [0,6])
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    : a 10 ∈ [0] ∧ a 26 ∈ [0,1] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0,1] ∧ a 12 ∈ [0,1,4,5] := by
  have b0 : a 10 ≠ 4 := exclude [0,1] (edge r35) (a 10) (a 11) 4 d11 c35 (by decide +kernel)
  have t0 : a 10 ∈ [0,3,5] := remove (a 10) 4 [0,3,4,5] d10 b0
  have b1 : a 10 ≠ 5 := exclude [0,1] (edge r35) (a 10) (a 11) 5 d11 c35 (by decide +kernel)
  have t1 : a 10 ∈ [0,3] := remove (a 10) 5 [0,3,5] t0 b1
  have b2 : a 10 ≠ 3 := exclude [0] (edge r36) (a 10) (a 14) 3 d14 c36 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 3 [0,3] t1 b2
  have b3 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t2 c37 (by decide +kernel)
  have t3 : a 26 ∈ [0,1,3,4,5] := remove (a 26) 2 [0,1,2,3,4,5] d26 b3
  have b4 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t2 c37 (by decide +kernel)
  have t4 : a 26 ∈ [0,1,4,5] := remove (a 26) 3 [0,1,3,4,5] t3 b4
  have b5 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t2 c37 (by decide +kernel)
  have t5 : a 26 ∈ [0,1,5] := remove (a 26) 4 [0,1,4,5] t4 b5
  have b6 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 t2 c37 (by decide +kernel)
  have t6 : a 26 ∈ [0,1] := remove (a 26) 5 [0,1,5] t5 b6
  have b7 : a 15 ≠ 1 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t7 : a 15 ∈ [0,2] := remove (a 15) 1 [0,1,2] d15 b7
  have b8 : a 15 ≠ 2 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 2 d11 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0] := remove (a 15) 2 [0,2] t7 b8
  have b9 : a 27 ≠ 2 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0,1] := remove (a 27) 2 [0,1,2] d27 b9
  have b10 : a 12 ≠ 2 := exclude [0,6] (edge r40) (a 12) (a 13) 2 d13 c40 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,3,4,5,6,7,10,11] := remove (a 12) 2 [0,1,2,3,4,5,6,7,10,11] d12 b10
  have b11 : a 12 ≠ 3 := exclude [0,6] (edge r40) (a 12) (a 13) 3 d13 c40 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,4,5,6,7,10,11] := remove (a 12) 3 [0,1,3,4,5,6,7,10,11] t10 b11
  have b12 : a 12 ≠ 6 := exclude [0] (edge r41) (a 12) (a 14) 6 d14 c41 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,4,5,7,10,11] := remove (a 12) 6 [0,1,4,5,6,7,10,11] t11 b12
  have b13 : a 12 ≠ 7 := exclude [0] (edge r41) (a 12) (a 14) 7 d14 c41 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,4,5,10,11] := remove (a 12) 7 [0,1,4,5,7,10,11] t12 b13
  have b14 : a 12 ≠ 10 := exclude [0] (edge r41) (a 12) (a 14) 10 d14 c41 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,4,5,11] := remove (a 12) 10 [0,1,4,5,10,11] t13 b14
  have b15 : a 12 ≠ 11 := exclude [0] (edge r41) (a 12) (a 14) 11 d14 c41 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,4,5] := remove (a 12) 11 [0,1,4,5,11] t14 b15
  exact And.intro t2 (And.intro t6 (And.intro t8 (And.intro t9 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (d12 : a 12 ∈ [0,1,4,5])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,6])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d14 : a 14 ∈ [0])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 28 ∈ [0,2,3,5,6] ∧ a 29 ∈ [0,2,4,5] ∧ a 30 ∈ [0,2] := by
  have b0 : a 28 ≠ 1 := exclude [0,1,4,5] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,3,4,5,6,7,8] := remove (a 28) 1 [0,1,2,3,4,5,6,7,8] d28 b0
  have b1 : a 28 ≠ 4 := exclude [0,1,4,5] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,3,5,6,7,8] := remove (a 28) 4 [0,2,3,4,5,6,7,8] t0 b1
  have b2 : a 28 ≠ 7 := exclude [0,1,4,5] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,3,5,6,8] := remove (a 28) 7 [0,2,3,5,6,7,8] t1 b2
  have b3 : a 28 ≠ 8 := exclude [0,1,4,5] (fun u v => edge r42 v u) (a 28) (a 12) 8 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2,3,5,6] := remove (a 28) 8 [0,2,3,5,6,8] t2 b3
  have b4 : a 29 ≠ 1 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t4 : a 29 ∈ [0,2,3,4,5] := remove (a 29) 1 [0,1,2,3,4,5] d29 b4
  have b5 : a 29 ≠ 3 := exclude [0,6] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t5 : a 29 ∈ [0,2,4,5] := remove (a 29) 3 [0,2,3,4,5] t4 b5
  have b6 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 30) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d30 b6
  have b7 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,4,5,6,7,8,9,10,11] := remove (a 30) 3 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,2,5,6,7,8,9,10,11] := remove (a 30) 4 [0,2,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,6,7,8,9,10,11] := remove (a 30) 5 [0,2,5,6,7,8,9,10,11] t8 b9
  have b10 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,7,8,9,10,11] := remove (a 30) 6 [0,2,6,7,8,9,10,11] t9 b10
  have b11 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0,2,8,9,10,11] := remove (a 30) 7 [0,2,7,8,9,10,11] t10 b11
  have b12 : a 30 ≠ 8 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 8 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,2,9,10,11] := remove (a 30) 8 [0,2,8,9,10,11] t11 b12
  have b13 : a 30 ≠ 9 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 9 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,2,10,11] := remove (a 30) 9 [0,2,9,10,11] t12 b13
  have b14 : a 30 ≠ 10 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 10 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,2,11] := remove (a 30) 10 [0,2,10,11] t13 b14
  have b15 : a 30 ≠ 11 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 11 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,2] := remove (a 30) 11 [0,2,11] t14 b15
  exact And.intro t3 (And.intro t5 (t15))

theorem chunk4 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,2])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0])
    (d21 : a 21 ∈ [0,1,2])
    (d17 : a 17 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3,4,5])
    (d19 : a 19 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,2,3,5,6])
    (d29 : a 29 ∈ [0,2,4,5])
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    : a 31 ∈ [0,1] ∧ a 16 ∈ [0] ∧ a 21 ∈ [0] ∧ a 18 ∈ [0] ∧ a 23 ∈ [0,1] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0,4,5] := by
  have b0 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0,1] := remove (a 31) 2 [0,1,2] d31 b0
  have b1 : a 16 ≠ 1 := exclude [0] (edge r50) (a 16) (a 20) 1 d20 c50 (by decide +kernel)
  have t1 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b1
  have b2 : a 16 ≠ 2 := exclude [0] (edge r50) (a 16) (a 20) 2 d20 c50 (by decide +kernel)
  have t2 : a 16 ∈ [0,3] := remove (a 16) 2 [0,2,3] t1 b2
  have b3 : a 16 ≠ 3 := exclude [0] (edge r50) (a 16) (a 20) 3 d20 c50 (by decide +kernel)
  have t3 : a 16 ∈ [0] := remove (a 16) 3 [0,3] t2 b3
  have b4 : a 21 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r53 v u) (a 21) (a 17) 1 d17 c53 (by decide +kernel)
  have t4 : a 21 ∈ [0,2] := remove (a 21) 1 [0,1,2] d21 b4
  have b5 : a 18 ≠ 1 := exclude [0] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t5 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b5
  have b6 : a 23 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,1,3,4,5] := remove (a 23) 2 [0,1,2,3,4,5] d23 b6
  have b7 : a 23 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t7 : a 23 ∈ [0,1,4,5] := remove (a 23) 3 [0,1,3,4,5] t6 b7
  have b8 : a 21 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 2 d20 c60 (by decide +kernel)
  have t8 : a 21 ∈ [0] := remove (a 21) 2 [0,2] t4 b8
  have b9 : a 28 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 2 d20 c62 (by decide +kernel)
  have t9 : a 28 ∈ [0,3,5,6] := remove (a 28) 2 [0,2,3,5,6] d28 b9
  have b10 : a 28 ≠ 3 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 3 d20 c62 (by decide +kernel)
  have t10 : a 28 ∈ [0,5,6] := remove (a 28) 3 [0,3,5,6] t9 b10
  have b11 : a 28 ≠ 5 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 5 d20 c62 (by decide +kernel)
  have t11 : a 28 ∈ [0,6] := remove (a 28) 5 [0,5,6] t10 b11
  have b12 : a 28 ≠ 6 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 6 d20 c62 (by decide +kernel)
  have t12 : a 28 ∈ [0] := remove (a 28) 6 [0,6] t11 b12
  have b13 : a 23 ≠ 4 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 4 t8 c63 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,5] := remove (a 23) 4 [0,1,4,5] t7 b13
  have b14 : a 23 ≠ 5 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 5 t8 c63 (by decide +kernel)
  have t14 : a 23 ∈ [0,1] := remove (a 23) 5 [0,1,5] t13 b14
  have b15 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 t8 c64 (by decide +kernel)
  have t15 : a 29 ∈ [0,4,5] := remove (a 29) 2 [0,2,4,5] d29 b15
  exact And.intro t0 (And.intro t3 (And.intro t8 (And.intro t5 (And.intro t14 (And.intro t12 (t15))))))

theorem chunk5 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,4,5])
    (d21 : a 21 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3,4,5])
    (d26 : a 26 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3,4,5])
    (d27 : a 27 ∈ [0,1])
    (d8 : a 8 ∈ [0,1,2,3,4,5,6,7,10,11])
    (d9 : a 9 ∈ [0,6])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 29 ∈ [0] ∧ a 31 ∈ [0] ∧ a 24 ∈ [0,1] ∧ a 25 ∈ [0] ∧ a 27 ∈ [0] ∧ a 8 ∈ [0,4,5,6,7,10,11] := by
  have b0 : a 29 ≠ 5 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 5 d21 c64 (by decide +kernel)
  have t0 : a 29 ∈ [0,4] := remove (a 29) 5 [0,4,5] d29 b0
  have b1 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 1 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b1
  have b2 : a 24 ≠ 2 := exclude [0,1] (edge r69) (a 24) (a 26) 2 d26 c69 (by decide +kernel)
  have t2 : a 24 ∈ [0,1,3,4,5] := remove (a 24) 2 [0,1,2,3,4,5] d24 b2
  have b3 : a 24 ≠ 3 := exclude [0,1] (edge r69) (a 24) (a 26) 3 d26 c69 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,4,5] := remove (a 24) 3 [0,1,3,4,5] t2 b3
  have b4 : a 24 ≠ 4 := exclude [0,1] (edge r69) (a 24) (a 26) 4 d26 c69 (by decide +kernel)
  have t4 : a 24 ∈ [0,1,5] := remove (a 24) 4 [0,1,4,5] t3 b4
  have b5 : a 24 ≠ 5 := exclude [0,1] (edge r69) (a 24) (a 26) 5 d26 c69 (by decide +kernel)
  have t5 : a 24 ∈ [0,1] := remove (a 24) 5 [0,1,5] t4 b5
  have b6 : a 25 ≠ 4 := exclude [0,1] (edge r71) (a 25) (a 27) 4 d27 c71 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,2,3,5] := remove (a 25) 4 [0,1,2,3,4,5] d25 b6
  have b7 : a 25 ≠ 5 := exclude [0,1] (edge r71) (a 25) (a 27) 5 d27 c71 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,2,3] := remove (a 25) 5 [0,1,2,3,5] t6 b7
  have b8 : a 25 ≠ 1 := exclude [0,4] (edge r72) (a 25) (a 29) 1 t0 c72 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] t7 b8
  have b9 : a 25 ≠ 2 := exclude [0,4] (edge r72) (a 25) (a 29) 2 t0 c72 (by decide +kernel)
  have t9 : a 25 ∈ [0,3] := remove (a 25) 2 [0,2,3] t8 b9
  have b10 : a 25 ≠ 3 := exclude [0,4] (edge r72) (a 25) (a 29) 3 t0 c72 (by decide +kernel)
  have t10 : a 25 ∈ [0] := remove (a 25) 3 [0,3] t9 b10
  have b11 : a 29 ≠ 4 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 4 t10 c72 (by decide +kernel)
  have t11 : a 29 ∈ [0] := remove (a 29) 4 [0,4] t0 b11
  have b12 : a 27 ≠ 1 := exclude [0,1] (fun u v => edge r73 v u) (a 27) (a 26) 1 d26 c73 (by decide +kernel)
  have t12 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b12
  have b13 : a 8 ≠ 1 := exclude [0,6] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t13 : a 8 ∈ [0,2,3,4,5,6,7,10,11] := remove (a 8) 1 [0,1,2,3,4,5,6,7,10,11] d8 b13
  have b14 : a 8 ≠ 2 := exclude [0,6] (edge r28) (a 8) (a 9) 2 d9 c28 (by decide +kernel)
  have t14 : a 8 ∈ [0,3,4,5,6,7,10,11] := remove (a 8) 2 [0,2,3,4,5,6,7,10,11] t13 b14
  have b15 : a 8 ≠ 3 := exclude [0,6] (edge r28) (a 8) (a 9) 3 d9 c28 (by decide +kernel)
  have t15 : a 8 ∈ [0,4,5,6,7,10,11] := remove (a 8) 3 [0,3,4,5,6,7,10,11] t14 b15
  exact And.intro t11 (And.intro t1 (And.intro t5 (And.intro t10 (And.intro t12 (t15)))))

theorem chunk6 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,4,5,6,7,10,11])
    (d9 : a 9 ∈ [0,6])
    (d10 : a 10 ∈ [0])
    (d12 : a 12 ∈ [0,1,4,5])
    (d11 : a 11 ∈ [0,1])
    (d13 : a 13 ∈ [0,6])
    (d17 : a 17 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 11 ∈ [0] ∧ a 13 ∈ [0] ∧ a 17 ∈ [0] ∧ a 19 ∈ [0,3] := by
  have b0 : a 8 ≠ 4 := exclude [0,6] (edge r28) (a 8) (a 9) 4 d9 c28 (by decide +kernel)
  have t0 : a 8 ∈ [0,5,6,7,10,11] := remove (a 8) 4 [0,4,5,6,7,10,11] d8 b0
  have b1 : a 8 ≠ 5 := exclude [0,6] (edge r28) (a 8) (a 9) 5 d9 c28 (by decide +kernel)
  have t1 : a 8 ∈ [0,6,7,10,11] := remove (a 8) 5 [0,5,6,7,10,11] t0 b1
  have b2 : a 8 ≠ 7 := exclude [0,6] (edge r28) (a 8) (a 9) 7 d9 c28 (by decide +kernel)
  have t2 : a 8 ∈ [0,6,10,11] := remove (a 8) 7 [0,6,7,10,11] t1 b2
  have b3 : a 8 ≠ 10 := exclude [0,6] (edge r28) (a 8) (a 9) 10 d9 c28 (by decide +kernel)
  have t3 : a 8 ∈ [0,6,11] := remove (a 8) 10 [0,6,10,11] t2 b3
  have b4 : a 8 ≠ 11 := exclude [0,6] (edge r28) (a 8) (a 9) 11 d9 c28 (by decide +kernel)
  have t4 : a 8 ∈ [0,6] := remove (a 8) 11 [0,6,11] t3 b4
  have b5 : a 8 ≠ 6 := exclude [0] (edge r29) (a 8) (a 10) 6 d10 c29 (by decide +kernel)
  have t5 : a 8 ∈ [0] := remove (a 8) 6 [0,6] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 t5 c30 (by decide +kernel)
  have t6 : a 12 ∈ [0,4,5] := remove (a 12) 1 [0,1,4,5] d12 b6
  have b7 : a 12 ≠ 4 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 4 t5 c30 (by decide +kernel)
  have t7 : a 12 ∈ [0,5] := remove (a 12) 4 [0,4,5] t6 b7
  have b8 : a 12 ≠ 5 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 5 t5 c30 (by decide +kernel)
  have t8 : a 12 ∈ [0] := remove (a 12) 5 [0,5] t7 b8
  have b9 : a 11 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 1 d10 c35 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b9
  have b10 : a 13 ≠ 6 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 6 t8 c40 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 6 [0,6] d13 b10
  have b11 : a 17 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 1 d16 c48 (by decide +kernel)
  have t11 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b11
  have b12 : a 17 ≠ 2 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 2 d16 c48 (by decide +kernel)
  have t12 : a 17 ∈ [0,3] := remove (a 17) 2 [0,2,3] t11 b12
  have b13 : a 17 ≠ 3 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 3 d16 c48 (by decide +kernel)
  have t13 : a 17 ∈ [0] := remove (a 17) 3 [0,3] t12 b13
  have b14 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 1 t13 c52 (by decide +kernel)
  have t14 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b14
  have b15 : a 19 ≠ 2 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 2 t13 c52 (by decide +kernel)
  have t15 : a 19 ∈ [0,3] := remove (a 19) 2 [0,2,3] t14 b15
  exact And.intro t5 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t13 (t15)))))

theorem chunk7 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,3])
    (d17 : a 17 ∈ [0])
    (d23 : a 23 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d9 : a 9 ∈ [0,6])
    (d8 : a 8 ∈ [0])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 19 ∈ [0] ∧ a 23 ∈ [0] ∧ a 24 ∈ [0] ∧ a 26 ∈ [0] ∧ a 30 ∈ [0] ∧ a 9 ∈ [0] := by
  have b0 : a 19 ≠ 3 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 3 d17 c52 (by decide +kernel)
  have t0 : a 19 ∈ [0] := remove (a 19) 3 [0,3] d19 b0
  have b1 : a 23 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 1 t0 c58 (by decide +kernel)
  have t1 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b1
  have b2 : a 24 ≠ 1 := exclude [0] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b2
  have b3 : a 26 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 26) (a 24) 1 t2 c69 (by decide +kernel)
  have t3 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b3
  have b4 : a 30 ≠ 2 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 2 t3 c74 (by decide +kernel)
  have t4 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b4
  have b5 : a 9 ≠ 6 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 6 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0] := remove (a 9) 6 [0,6] d9 b5
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (t5)))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0])
    (start5 : a 5 ∈ [0])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0])
    (start8 : a 8 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (start14 : a 14 ∈ [0,1])
    (start15 : a 15 ∈ [0,1,2])
    (start16 : a 16 ∈ [0,1,2,3])
    (start17 : a 17 ∈ [0,1,2,3])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1,2,3])
    (start20 : a 20 ∈ [0,1])
    (start21 : a 21 ∈ [0,1,2])
    (start22 : a 22 ∈ [0,1])
    (start23 : a 23 ∈ [0,1,2,3,4,5])
    (start24 : a 24 ∈ [0,1,2,3,4,5])
    (start25 : a 25 ∈ [0,1,2,3,4,5])
    (start26 : a 26 ∈ [0,1,2,3,4,5])
    (start27 : a 27 ∈ [0,1,2])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7,8])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
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
  have group1 := chunk0 a start3 start11 start6 start4 start12 start20 start13 start5 start14 start22 c14 c17 c18 c19 c21 c24 c25
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8,h9⟩
  have group10 := chunk1 a start8 h5 start9 h3 h7 start10 c30 c32 c33 c35
  rcases group10 with ⟨h11,h12,h13,h14⟩
  have group15 := chunk2 a h14 h3 h8 start26 start15 start27 h5 h13 c35 c36 c37 c38 c39 c40 c41
  rcases group15 with ⟨h16,h17,h18,h19,h20⟩
  have group21 := chunk3 a start28 h20 start29 h13 start30 h8 c42 c44 c46
  rcases group21 with ⟨h22,h23,h24⟩
  have group25 := chunk4 a start31 h18 start16 h6 start21 start17 start18 h9 start23 start19 h22 h23 c47 c50 c53 c56 c58 c60 c62 c63 c64
  rcases group25 with ⟨h26,h27,h28,h29,h30,h31,h32⟩
  have group33 := chunk5 a h32 h28 h26 h30 start24 h17 start25 h19 h11 h12 c28 c64 c67 c69 c71 c72 c73
  rcases group33 with ⟨h34,h35,h36,h37,h38,h39⟩
  have group40 := chunk6 a h39 h12 h16 h20 h3 h13 start17 h27 start19 c28 c29 c30 c35 c40 c48 c52
  rcases group40 with ⟨h41,h42,h43,h44,h45,h46⟩
  have group47 := chunk7 a h46 h45 h30 h36 h37 h17 h24 h12 h41 c28 c52 c58 c68 c69 c74
  rcases group47 with ⟨h48,h49,h50,h51,h52,h53⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h2) (And.intro (forced (a 4) 0 start4) (And.intro (forced (a 5) 0 start5) (And.intro (forced (a 6) 0 h4) (And.intro (forced (a 7) 0 start7) (And.intro (forced (a 8) 0 h41) (And.intro (forced (a 9) 0 h53) (And.intro (forced (a 10) 0 h16) (And.intro (forced (a 11) 0 h43) (And.intro (forced (a 12) 0 h42) (And.intro (forced (a 13) 0 h44) (And.intro (forced (a 14) 0 h8) (And.intro (forced (a 15) 0 h18) (And.intro (forced (a 16) 0 h27) (And.intro (forced (a 17) 0 h45) (And.intro (forced (a 18) 0 h29) (And.intro (forced (a 19) 0 h48) (And.intro (forced (a 20) 0 h6) (And.intro (forced (a 21) 0 h28) (And.intro (forced (a 22) 0 h9) (And.intro (forced (a 23) 0 h49) (And.intro (forced (a 24) 0 h50) (And.intro (forced (a 25) 0 h37) (And.intro (forced (a 26) 0 h51) (And.intro (forced (a 27) 0 h38) (And.intro (forced (a 28) 0 h31) (And.intro (forced (a 29) 0 h34) (And.intro (forced (a 30) 0 h52) (forced (a 31) 0 h35)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_178
