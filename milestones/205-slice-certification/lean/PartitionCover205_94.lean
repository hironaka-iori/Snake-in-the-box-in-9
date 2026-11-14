import FiniteDomain205
namespace PartitionCover205_94
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[3]
def r5 : Array Nat := #[15]
def r6 : Array Nat := #[5]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[15]
def r10 : Array Nat := #[3,12]
def r11 : Array Nat := #[7,14]
def r12 : Array Nat := #[1,2,4,8,16,32,64,128]
def r13 : Array Nat := #[1,2,4,8,16,32,64,128]
def r14 : Array Nat := #[3,3,48,48,0,0,0,0]
def r15 : Array Nat := #[1,1,2,2,4,4,8,8]
def r16 : Array Nat := #[51,51,51,51,0,0,0,0]
def r17 : Array Nat := #[5,5,10,10,5,5,10,10]
def r18 : Array Nat := #[1,3,4,12,0,0,0,0]
def r19 : Array Nat := #[5,1280,5,1280]
def r20 : Array Nat := #[1,2,4,8]
def r21 : Array Nat := #[1,2,4,8]
def r22 : Array Nat := #[1,4,16,64]
def r23 : Array Nat := #[1,0,0,0]
def r24 : Array Nat := #[51,204,51,204]
def r25 : Array Nat := #[1,0,0,0]
def r26 : Array Nat := #[1,2,4,8]
def r27 : Array Nat := #[5,0,0,0]
def r28 : Array Nat := #[1,2,4,8,16,32,64,128]
def r29 : Array Nat := #[1,1,2,2,4,4,8,8]
def r30 : Array Nat := #[3,12,48,192,768,3072,12288,49152]
def r31 : Array Nat := #[15,240,3840,61440]
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    : a 4 ∈ [0,1] ∧ a 8 ∈ [0,1] ∧ a 5 ∈ [0,1,2,3] ∧ a 9 ∈ [0,2] ∧ a 3 ∈ [0] ∧ a 6 ∈ [0,2,3,4,5,6,7] := by
  have b0 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,3,4,5,6,7] := remove (a 4) 2 [0,1,2,3,4,5,6,7] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,4,5,6,7] := remove (a 4) 3 [0,1,3,4,5,6,7] t0 b1
  have b2 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,5,6,7] := remove (a 4) 4 [0,1,4,5,6,7] t1 b2
  have b3 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,6,7] := remove (a 4) 5 [0,1,5,6,7] t2 b3
  have b4 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,1,7] := remove (a 4) 6 [0,1,6,7] t3 b4
  have b5 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,1] := remove (a 4) 7 [0,1,7] t4 b5
  have b6 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b6
  have b7 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t7 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t6 b7
  have b8 : a 5 ≠ 4 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 4 d1 c5 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,2,3,5,6,7] := remove (a 5) 4 [0,1,2,3,4,5,6,7] d5 b8
  have b9 : a 5 ≠ 5 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 5 d1 c5 (by decide +kernel)
  have t9 : a 5 ∈ [0,1,2,3,6,7] := remove (a 5) 5 [0,1,2,3,5,6,7] t8 b9
  have b10 : a 5 ≠ 6 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 6 d1 c5 (by decide +kernel)
  have t10 : a 5 ∈ [0,1,2,3,7] := remove (a 5) 6 [0,1,2,3,6,7] t9 b10
  have b11 : a 5 ≠ 7 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 7 d1 c5 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,2,3] := remove (a 5) 7 [0,1,2,3,7] t10 b11
  have b12 : a 9 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 1 d1 c6 (by decide +kernel)
  have t12 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b12
  have b13 : a 9 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 3 d1 c6 (by decide +kernel)
  have t13 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t12 b13
  have b14 : a 3 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 1 d2 c7 (by decide +kernel)
  have t14 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b14
  have b15 : a 6 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 1 d2 c8 (by decide +kernel)
  have t15 : a 6 ∈ [0,2,3,4,5,6,7] := remove (a 6) 1 [0,1,2,3,4,5,6,7] d6 b15
  exact And.intro t5 (And.intro t7 (And.intro t11 (And.intro t13 (And.intro t14 (t15)))))

theorem chunk1 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,2,3,4,5,6,7])
    (d2 : a 2 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (c8 : edge r8 (a 2) (a 6)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 6 ∈ [0] ∧ a 7 ∈ [0,1] ∧ a 11 ∈ [0,1,2] ∧ a 5 ∈ [0,1] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0,1,6,7] := by
  have b0 : a 6 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 2 d2 c8 (by decide +kernel)
  have t0 : a 6 ∈ [0,3,4,5,6,7] := remove (a 6) 2 [0,2,3,4,5,6,7] d6 b0
  have b1 : a 6 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 3 d2 c8 (by decide +kernel)
  have t1 : a 6 ∈ [0,4,5,6,7] := remove (a 6) 3 [0,3,4,5,6,7] t0 b1
  have b2 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 d2 c8 (by decide +kernel)
  have t2 : a 6 ∈ [0,5,6,7] := remove (a 6) 4 [0,4,5,6,7] t1 b2
  have b3 : a 6 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 5 d2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0,6,7] := remove (a 6) 5 [0,5,6,7] t2 b3
  have b4 : a 6 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 6 d2 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0,7] := remove (a 6) 6 [0,6,7] t3 b4
  have b5 : a 6 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 7 d2 c8 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 7 [0,7] t4 b5
  have b6 : a 7 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 2 d3 c10 (by decide +kernel)
  have t6 : a 7 ∈ [0,1,3] := remove (a 7) 2 [0,1,2,3] d7 b6
  have b7 : a 7 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 3 d3 c10 (by decide +kernel)
  have t7 : a 7 ∈ [0,1] := remove (a 7) 3 [0,1,3] t6 b7
  have b8 : a 11 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t8 : a 11 ∈ [0,1,2] := remove (a 11) 3 [0,1,2,3] d11 b8
  have b9 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 2 d4 c12 (by decide +kernel)
  have t9 : a 5 ∈ [0,1,3] := remove (a 5) 2 [0,1,2,3] d5 b9
  have b10 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 3 d4 c12 (by decide +kernel)
  have t10 : a 5 ∈ [0,1] := remove (a 5) 3 [0,1,3] t9 b10
  have b11 : a 4 ≠ 1 := exclude [0] (edge r13) (a 4) (a 6) 1 t5 c13 (by decide +kernel)
  have t11 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b11
  have b12 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t11 c14 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,3,4,5,6,7] := remove (a 12) 2 [0,1,2,3,4,5,6,7] d12 b12
  have b13 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t11 c14 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,4,5,6,7] := remove (a 12) 3 [0,1,3,4,5,6,7] t12 b13
  have b14 : a 12 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 4 t11 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,5,6,7] := remove (a 12) 4 [0,1,4,5,6,7] t13 b14
  have b15 : a 12 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 5 t11 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,6,7] := remove (a 12) 5 [0,1,5,6,7] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t11 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,6,7])
    (d4 : a 4 ∈ [0])
    (d7 : a 7 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (d14 : a 14 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 12 ∈ [0,1] ∧ a 7 ∈ [0] ∧ a 13 ∈ [0,1,4,5] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0,2,8,9,10,11,12,13,14,15] := by
  have b0 : a 12 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 6 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,7] := remove (a 12) 6 [0,1,6,7] d12 b0
  have b1 : a 12 ≠ 7 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 7 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,1] := remove (a 12) 7 [0,1,7] t0 b1
  have b2 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r15 v u) (a 7) (a 5) 1 d5 c15 (by decide +kernel)
  have t2 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b2
  have b3 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,3,4,5,6,7] := remove (a 13) 2 [0,1,2,3,4,5,6,7] d13 b3
  have b4 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,4,5,6,7] := remove (a 13) 3 [0,1,3,4,5,6,7] t3 b4
  have b5 : a 13 ≠ 6 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,4,5,7] := remove (a 13) 6 [0,1,4,5,6,7] t4 b5
  have b6 : a 13 ≠ 7 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,4,5] := remove (a 13) 7 [0,1,4,5,7] t5 b6
  have b7 : a 14 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 1 d6 c18 (by decide +kernel)
  have t7 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b7
  have b8 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 d6 c18 (by decide +kernel)
  have t8 : a 14 ∈ [0,3] := remove (a 14) 2 [0,2,3] t7 b8
  have b9 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 d6 c18 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 3 [0,3] t8 b9
  have b10 : a 15 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 1 t2 c19 (by decide +kernel)
  have t10 : a 15 ∈ [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 15) 1 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] d15 b10
  have b11 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 t2 c19 (by decide +kernel)
  have t11 : a 15 ∈ [0,2,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 15) 3 [0,2,3,4,5,6,7,8,9,10,11,12,13,14,15] t10 b11
  have b12 : a 15 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 4 t2 c19 (by decide +kernel)
  have t12 : a 15 ∈ [0,2,5,6,7,8,9,10,11,12,13,14,15] := remove (a 15) 4 [0,2,4,5,6,7,8,9,10,11,12,13,14,15] t11 b12
  have b13 : a 15 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 5 t2 c19 (by decide +kernel)
  have t13 : a 15 ∈ [0,2,6,7,8,9,10,11,12,13,14,15] := remove (a 15) 5 [0,2,5,6,7,8,9,10,11,12,13,14,15] t12 b13
  have b14 : a 15 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 6 t2 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,2,7,8,9,10,11,12,13,14,15] := remove (a 15) 6 [0,2,6,7,8,9,10,11,12,13,14,15] t13 b14
  have b15 : a 15 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 7 t2 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,2,8,9,10,11,12,13,14,15] := remove (a 15) 7 [0,2,7,8,9,10,11,12,13,14,15] t14 b15
  exact And.intro t1 (And.intro t2 (And.intro t6 (And.intro t9 (t15))))

theorem chunk3 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,2,8,9,10,11,12,13,14,15])
    (d7 : a 7 ∈ [0])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2])
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    : a 15 ∈ [0,2] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 10 ∈ [0] ∧ a 12 ∈ [0] ∧ a 11 ∈ [0] := by
  have b0 : a 15 ≠ 8 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 8 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,2,9,10,11,12,13,14,15] := remove (a 15) 8 [0,2,8,9,10,11,12,13,14,15] d15 b0
  have b1 : a 15 ≠ 9 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 9 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,2,10,11,12,13,14,15] := remove (a 15) 9 [0,2,9,10,11,12,13,14,15] t0 b1
  have b2 : a 15 ≠ 10 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 10 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,2,11,12,13,14,15] := remove (a 15) 10 [0,2,10,11,12,13,14,15] t1 b2
  have b3 : a 15 ≠ 11 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 11 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,2,12,13,14,15] := remove (a 15) 11 [0,2,11,12,13,14,15] t2 b3
  have b4 : a 15 ≠ 12 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 12 d7 c19 (by decide +kernel)
  have t4 : a 15 ∈ [0,2,13,14,15] := remove (a 15) 12 [0,2,12,13,14,15] t3 b4
  have b5 : a 15 ≠ 13 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 13 d7 c19 (by decide +kernel)
  have t5 : a 15 ∈ [0,2,14,15] := remove (a 15) 13 [0,2,13,14,15] t4 b5
  have b6 : a 15 ≠ 14 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 14 d7 c19 (by decide +kernel)
  have t6 : a 15 ∈ [0,2,15] := remove (a 15) 14 [0,2,14,15] t5 b6
  have b7 : a 15 ≠ 15 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 15 d7 c19 (by decide +kernel)
  have t7 : a 15 ∈ [0,2] := remove (a 15) 15 [0,2,15] t6 b7
  have b8 : a 8 ≠ 1 := exclude [0,2] (edge r20) (a 8) (a 9) 1 d9 c20 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b8
  have b9 : a 9 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 9) (a 8) 2 t8 c20 (by decide +kernel)
  have t9 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b9
  have b10 : a 10 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 1 t8 c21 (by decide +kernel)
  have t10 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b10
  have b11 : a 10 ≠ 2 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 2 t8 c21 (by decide +kernel)
  have t11 : a 10 ∈ [0,3] := remove (a 10) 2 [0,2,3] t10 b11
  have b12 : a 10 ≠ 3 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 3 t8 c21 (by decide +kernel)
  have t12 : a 10 ∈ [0] := remove (a 10) 3 [0,3] t11 b12
  have b13 : a 12 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 8) 1 t8 c22 (by decide +kernel)
  have t13 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b13
  have b14 : a 11 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 11) (a 9) 1 t9 c23 (by decide +kernel)
  have t14 : a 11 ∈ [0,2] := remove (a 11) 1 [0,1,2] d11 b14
  have b15 : a 11 ≠ 2 := exclude [0] (fun u v => edge r23 v u) (a 11) (a 9) 2 t9 c23 (by decide +kernel)
  have t15 : a 11 ∈ [0] := remove (a 11) 2 [0,2] t14 b15
  exact And.intro t7 (And.intro t8 (And.intro t9 (And.intro t12 (And.intro t13 (t15)))))

theorem chunk4 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,4,5])
    (d12 : a 12 ∈ [0])
    (d15 : a 15 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (c12 : edge r12 (a 4) (a 5)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    : a 13 ∈ [0] ∧ a 15 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 13 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 13) (a 12) 1 d12 c28 (by decide +kernel)
  have t0 : a 13 ∈ [0,4,5] := remove (a 13) 1 [0,1,4,5] d13 b0
  have b1 : a 13 ≠ 4 := exclude [0] (fun u v => edge r28 v u) (a 13) (a 12) 4 d12 c28 (by decide +kernel)
  have t1 : a 13 ∈ [0,5] := remove (a 13) 4 [0,4,5] t0 b1
  have b2 : a 13 ≠ 5 := exclude [0] (fun u v => edge r28 v u) (a 13) (a 12) 5 d12 c28 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 5 [0,5] t1 b2
  have b3 : a 15 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 15) (a 13) 2 t2 c30 (by decide +kernel)
  have t3 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b3
  have b4 : a 5 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 1 d4 c12 (by decide +kernel)
  have t4 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b4
  exact And.intro t2 (And.intro t3 (t4))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (start7 : a 7 ∈ [0,1,2,3])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    (c29 : edge r29 (a 12) (a 14)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    (c31 : edge r31 (a 14) (a 15)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0) := by
  have group1 := chunk0 a start4 start0 start8 start5 start1 start9 start3 start2 start6 c2 c3 c5 c6 c7 c8
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7⟩
  have group8 := chunk1 a h7 start2 start7 h6 start11 h4 h2 start12 c8 c10 c11 c12 c13 c14
  rcases group8 with ⟨h9,h10,h11,h12,h13,h14⟩
  have group15 := chunk2 a h14 h13 h10 h12 start13 start14 h9 start15 c14 c15 c16 c18 c19
  rcases group15 with ⟨h16,h17,h18,h19,h20⟩
  have group21 := chunk3 a h20 h17 h3 h5 start10 h16 h11 c19 c20 c21 c22 c23
  rcases group21 with ⟨h22,h23,h24,h25,h26,h27⟩
  have group28 := chunk4 a h18 h26 h22 h12 h13 c12 c28 c30
  rcases group28 with ⟨h29,h30,h31⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h6) (And.intro (forced (a 4) 0 h13) (And.intro (forced (a 5) 0 h31) (And.intro (forced (a 6) 0 h9) (And.intro (forced (a 7) 0 h17) (And.intro (forced (a 8) 0 h23) (And.intro (forced (a 9) 0 h24) (And.intro (forced (a 10) 0 h25) (And.intro (forced (a 11) 0 h27) (And.intro (forced (a 12) 0 h26) (And.intro (forced (a 13) 0 h29) (And.intro (forced (a 14) 0 h19) (forced (a 15) 0 h30)))))))))))))))
#print axioms cover
end PartitionCover205_94
