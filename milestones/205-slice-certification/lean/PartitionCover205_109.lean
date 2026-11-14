import FiniteDomain205
namespace PartitionCover205_109
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[3]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[51]
def r3 : Array Nat := #[15]
def r4 : Array Nat := #[15,240]
def r5 : Array Nat := #[50331651,197376]
def r6 : Array Nat := #[3,12]
def r7 : Array Nat := #[1,16,4,0,64,0]
def r8 : Array Nat := #[3,12,48,192,768,3072]
def r9 : Array Nat := #[1,2,4,8,16,32]
def r10 : Array Nat := #[1,2,4,8,1,16,32,64]
def r11 : Array Nat := #[1,0,4,0,2,0,16,0]
def r12 : Array Nat := #[3,12,48,192,768,3072,12288,49152,196608,786432,3145728,12582912,50331648,201326592,805306368,3221225472]
def r13 : Array Nat := #[17,0,17,0,260,0,260,0,0,0,0,0,0,0,0,0]
def r14 : Array Nat := #[1,1,1,1,2,2,2,2,4,4,4,4,8,8,8,8]
def r15 : Array Nat := #[1,1,0,0,4,4,0,0,1,1,0,0,32,32,0,0,1,1,32,32,0,0,0,0,1,1,4,4,0,0,0,0]
def r16 : Array Nat := #[1,0,0,0,2,0,0,0,1,0,0,0,4,0,0,0,1,0,4,0,0,0,0,0,1,0,2,0,0,0,0,0]
def r17 : Array Nat := #[1,0,1,0,4,0,4,0,32,0,32,0]
def r18 : Array Nat := #[63,0,63,0,63,0,63,0,63,0,63,0]
def r19 : Array Nat := #[3,1,12,4,2,48,16]
def r20 : Array Nat := #[1,4,0,0]
def r21 : Array Nat := #[3,3,0,0]
def r22 : Array Nat := #[1,2,4,8]
def r23 : Array Nat := #[5,5,18,18]
def r24 : Array Nat := #[1,2,1,4]
def r25 : Array Nat := #[1,2,4,8,16,32]
def r26 : Array Nat := #[1,2,4,8,16,32]
def r27 : Array Nat := #[1,2,4,8,16,32]
def r28 : Array Nat := #[1,1,0,0]
def r29 : Array Nat := #[3,3,0,0]
def r30 : Array Nat := #[3,12,48]
def r31 : Array Nat := #[1,2,4,8,16,32]
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    : a 2 ∈ [0] ∧ a 4 ∈ [0,1,4,5,15] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5] := remove (a 2) 1 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 2 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,3,4,5] := remove (a 2) 2 [0,2,3,4,5] t0 b1
  have b2 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,4,5] := remove (a 2) 3 [0,3,4,5] t1 b2
  have b3 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,5] := remove (a 2) 4 [0,4,5] t2 b3
  have b4 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 5 [0,5] t3 b4
  have b5 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 4) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] d4 b5
  have b6 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15] := remove (a 4) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15] t5 b6
  have b7 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,1,4,5,7,8,9,10,11,12,13,14,15] := remove (a 4) 6 [0,1,4,5,6,7,8,9,10,11,12,13,14,15] t6 b7
  have b8 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,1,4,5,8,9,10,11,12,13,14,15] := remove (a 4) 7 [0,1,4,5,7,8,9,10,11,12,13,14,15] t7 b8
  have b9 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,1,4,5,9,10,11,12,13,14,15] := remove (a 4) 8 [0,1,4,5,8,9,10,11,12,13,14,15] t8 b9
  have b10 : a 4 ≠ 9 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 9 d0 c2 (by decide +kernel)
  have t10 : a 4 ∈ [0,1,4,5,10,11,12,13,14,15] := remove (a 4) 9 [0,1,4,5,9,10,11,12,13,14,15] t9 b10
  have b11 : a 4 ≠ 10 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 10 d0 c2 (by decide +kernel)
  have t11 : a 4 ∈ [0,1,4,5,11,12,13,14,15] := remove (a 4) 10 [0,1,4,5,10,11,12,13,14,15] t10 b11
  have b12 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t12 : a 4 ∈ [0,1,4,5,12,13,14,15] := remove (a 4) 11 [0,1,4,5,11,12,13,14,15] t11 b12
  have b13 : a 4 ≠ 12 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 12 d0 c2 (by decide +kernel)
  have t13 : a 4 ∈ [0,1,4,5,13,14,15] := remove (a 4) 12 [0,1,4,5,12,13,14,15] t12 b13
  have b14 : a 4 ≠ 13 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 13 d0 c2 (by decide +kernel)
  have t14 : a 4 ∈ [0,1,4,5,14,15] := remove (a 4) 13 [0,1,4,5,13,14,15] t13 b14
  have b15 : a 4 ≠ 14 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 14 d0 c2 (by decide +kernel)
  have t15 : a 4 ∈ [0,1,4,5,15] := remove (a 4) 14 [0,1,4,5,14,15] t14 b15
  exact And.intro t4 (t15)

theorem chunk1 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,4,5,15])
    (d0 : a 0 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
    (d1 : a 1 ∈ [0,1])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    : a 4 ∈ [0,1,4,5] ∧ a 5 ∈ [0,1,8,9,16,17,21,22,23,24,25,26,27,28,29,30,31] := by
  have b0 : a 4 ≠ 15 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 15 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,4,5] := remove (a 4) 15 [0,1,4,5,15] d4 b0
  have b1 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 2 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 2 [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] d5 b1
  have b2 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 3 d1 c5 (by decide +kernel)
  have t2 : a 5 ∈ [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 3 [0,1,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t1 b2
  have b3 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 4 d1 c5 (by decide +kernel)
  have t3 : a 5 ∈ [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 4 [0,1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t2 b3
  have b4 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 5 d1 c5 (by decide +kernel)
  have t4 : a 5 ∈ [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 5 [0,1,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t3 b4
  have b5 : a 5 ≠ 6 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 6 d1 c5 (by decide +kernel)
  have t5 : a 5 ∈ [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 6 [0,1,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t4 b5
  have b6 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 7 d1 c5 (by decide +kernel)
  have t6 : a 5 ∈ [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 7 [0,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t5 b6
  have b7 : a 5 ≠ 10 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 10 d1 c5 (by decide +kernel)
  have t7 : a 5 ∈ [0,1,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 10 [0,1,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t6 b7
  have b8 : a 5 ≠ 11 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 11 d1 c5 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,8,9,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 11 [0,1,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t7 b8
  have b9 : a 5 ≠ 12 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 12 d1 c5 (by decide +kernel)
  have t9 : a 5 ∈ [0,1,8,9,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 12 [0,1,8,9,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t8 b9
  have b10 : a 5 ≠ 13 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 13 d1 c5 (by decide +kernel)
  have t10 : a 5 ∈ [0,1,8,9,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 13 [0,1,8,9,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t9 b10
  have b11 : a 5 ≠ 14 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 14 d1 c5 (by decide +kernel)
  have t11 : a 5 ∈ [0,1,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 14 [0,1,8,9,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t10 b11
  have b12 : a 5 ≠ 15 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 15 d1 c5 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,8,9,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 15 [0,1,8,9,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t11 b12
  have b13 : a 5 ≠ 18 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 18 d1 c5 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,8,9,16,17,19,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 18 [0,1,8,9,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31] t12 b13
  have b14 : a 5 ≠ 19 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 19 d1 c5 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,8,9,16,17,20,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 19 [0,1,8,9,16,17,19,20,21,22,23,24,25,26,27,28,29,30,31] t13 b14
  have b15 : a 5 ≠ 20 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 20 d1 c5 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,8,9,16,17,21,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 20 [0,1,8,9,16,17,20,21,22,23,24,25,26,27,28,29,30,31] t14 b15
  exact And.intro t0 (t15)

theorem chunk2 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,8,9,16,17,21,22,23,24,25,26,27,28,29,30,31])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0,1,2,3,4,5,6,7])
    (d2 : a 2 ∈ [0])
    (c5 : edge r5 (a 1) (a 5)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    : a 5 ∈ [0,1,8,9,16,17,24,25] ∧ a 3 ∈ [0] := by
  have b0 : a 5 ≠ 21 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 21 d1 c5 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,8,9,16,17,22,23,24,25,26,27,28,29,30,31] := remove (a 5) 21 [0,1,8,9,16,17,21,22,23,24,25,26,27,28,29,30,31] d5 b0
  have b1 : a 5 ≠ 22 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 22 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,8,9,16,17,23,24,25,26,27,28,29,30,31] := remove (a 5) 22 [0,1,8,9,16,17,22,23,24,25,26,27,28,29,30,31] t0 b1
  have b2 : a 5 ≠ 23 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 23 d1 c5 (by decide +kernel)
  have t2 : a 5 ∈ [0,1,8,9,16,17,24,25,26,27,28,29,30,31] := remove (a 5) 23 [0,1,8,9,16,17,23,24,25,26,27,28,29,30,31] t1 b2
  have b3 : a 5 ≠ 26 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 26 d1 c5 (by decide +kernel)
  have t3 : a 5 ∈ [0,1,8,9,16,17,24,25,27,28,29,30,31] := remove (a 5) 26 [0,1,8,9,16,17,24,25,26,27,28,29,30,31] t2 b3
  have b4 : a 5 ≠ 27 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 27 d1 c5 (by decide +kernel)
  have t4 : a 5 ∈ [0,1,8,9,16,17,24,25,28,29,30,31] := remove (a 5) 27 [0,1,8,9,16,17,24,25,27,28,29,30,31] t3 b4
  have b5 : a 5 ≠ 28 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 28 d1 c5 (by decide +kernel)
  have t5 : a 5 ∈ [0,1,8,9,16,17,24,25,29,30,31] := remove (a 5) 28 [0,1,8,9,16,17,24,25,28,29,30,31] t4 b5
  have b6 : a 5 ≠ 29 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 29 d1 c5 (by decide +kernel)
  have t6 : a 5 ∈ [0,1,8,9,16,17,24,25,30,31] := remove (a 5) 29 [0,1,8,9,16,17,24,25,29,30,31] t5 b6
  have b7 : a 5 ≠ 30 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 30 d1 c5 (by decide +kernel)
  have t7 : a 5 ∈ [0,1,8,9,16,17,24,25,31] := remove (a 5) 30 [0,1,8,9,16,17,24,25,30,31] t6 b7
  have b8 : a 5 ≠ 31 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 31 d1 c5 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,8,9,16,17,24,25] := remove (a 5) 31 [0,1,8,9,16,17,24,25,31] t7 b8
  have b9 : a 3 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 1 d2 c7 (by decide +kernel)
  have t9 : a 3 ∈ [0,2,3,4,5,6,7] := remove (a 3) 1 [0,1,2,3,4,5,6,7] d3 b9
  have b10 : a 3 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 2 d2 c7 (by decide +kernel)
  have t10 : a 3 ∈ [0,3,4,5,6,7] := remove (a 3) 2 [0,2,3,4,5,6,7] t9 b10
  have b11 : a 3 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 3 d2 c7 (by decide +kernel)
  have t11 : a 3 ∈ [0,4,5,6,7] := remove (a 3) 3 [0,3,4,5,6,7] t10 b11
  have b12 : a 3 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 4 d2 c7 (by decide +kernel)
  have t12 : a 3 ∈ [0,5,6,7] := remove (a 3) 4 [0,4,5,6,7] t11 b12
  have b13 : a 3 ≠ 5 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 5 d2 c7 (by decide +kernel)
  have t13 : a 3 ∈ [0,6,7] := remove (a 3) 5 [0,5,6,7] t12 b13
  have b14 : a 3 ≠ 6 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 6 d2 c7 (by decide +kernel)
  have t14 : a 3 ∈ [0,7] := remove (a 3) 6 [0,6,7] t13 b14
  have b15 : a 3 ≠ 7 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 7 d2 c7 (by decide +kernel)
  have t15 : a 3 ∈ [0] := remove (a 3) 7 [0,7] t14 b15
  exact And.intro t8 (t15)

theorem chunk3 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6])
    (d3 : a 3 ∈ [0])
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    : a 6 ∈ [0,1] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0,2,3,4,5,6] := by
  have b0 : a 6 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 2 d2 c8 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 6) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d6 b0
  have b1 : a 6 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 3 d2 c8 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 6) 3 [0,1,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 d2 c8 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 6) 4 [0,1,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 6 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 5 d2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,6,7,8,9,10,11] := remove (a 6) 5 [0,1,5,6,7,8,9,10,11] t2 b3
  have b4 : a 6 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 6 d2 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0,1,7,8,9,10,11] := remove (a 6) 6 [0,1,6,7,8,9,10,11] t3 b4
  have b5 : a 6 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 7 d2 c8 (by decide +kernel)
  have t5 : a 6 ∈ [0,1,8,9,10,11] := remove (a 6) 7 [0,1,7,8,9,10,11] t4 b5
  have b6 : a 6 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 8 d2 c8 (by decide +kernel)
  have t6 : a 6 ∈ [0,1,9,10,11] := remove (a 6) 8 [0,1,8,9,10,11] t5 b6
  have b7 : a 6 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 9 d2 c8 (by decide +kernel)
  have t7 : a 6 ∈ [0,1,10,11] := remove (a 6) 9 [0,1,9,10,11] t6 b7
  have b8 : a 6 ≠ 10 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 10 d2 c8 (by decide +kernel)
  have t8 : a 6 ∈ [0,1,11] := remove (a 6) 10 [0,1,10,11] t7 b8
  have b9 : a 6 ≠ 11 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 11 d2 c8 (by decide +kernel)
  have t9 : a 6 ∈ [0,1] := remove (a 6) 11 [0,1,11] t8 b9
  have b10 : a 10 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 1 d2 c9 (by decide +kernel)
  have t10 : a 10 ∈ [0,2,3,4,5] := remove (a 10) 1 [0,1,2,3,4,5] d10 b10
  have b11 : a 10 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 2 d2 c9 (by decide +kernel)
  have t11 : a 10 ∈ [0,3,4,5] := remove (a 10) 2 [0,2,3,4,5] t10 b11
  have b12 : a 10 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 3 d2 c9 (by decide +kernel)
  have t12 : a 10 ∈ [0,4,5] := remove (a 10) 3 [0,3,4,5] t11 b12
  have b13 : a 10 ≠ 4 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 4 d2 c9 (by decide +kernel)
  have t13 : a 10 ∈ [0,5] := remove (a 10) 4 [0,4,5] t12 b13
  have b14 : a 10 ≠ 5 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 5 d2 c9 (by decide +kernel)
  have t14 : a 10 ∈ [0] := remove (a 10) 5 [0,5] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 1 d3 c10 (by decide +kernel)
  have t15 : a 7 ∈ [0,2,3,4,5,6] := remove (a 7) 1 [0,1,2,3,4,5,6] d7 b15
  exact And.intro t9 (And.intro t14 (t15))

theorem chunk4 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2,3,4,5,6])
    (d3 : a 3 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d4 : a 4 ∈ [0,1,4,5])
    (d5 : a 5 ∈ [0,1,8,9,16,17,24,25])
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    : a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0,4] ∧ a 5 ∈ [0,1,8,9] := by
  have b0 : a 7 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 2 d3 c10 (by decide +kernel)
  have t0 : a 7 ∈ [0,3,4,5,6] := remove (a 7) 2 [0,2,3,4,5,6] d7 b0
  have b1 : a 7 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 3 d3 c10 (by decide +kernel)
  have t1 : a 7 ∈ [0,4,5,6] := remove (a 7) 3 [0,3,4,5,6] t0 b1
  have b2 : a 7 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 4 d3 c10 (by decide +kernel)
  have t2 : a 7 ∈ [0,5,6] := remove (a 7) 4 [0,4,5,6] t1 b2
  have b3 : a 7 ≠ 5 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 5 d3 c10 (by decide +kernel)
  have t3 : a 7 ∈ [0,6] := remove (a 7) 5 [0,5,6] t2 b3
  have b4 : a 7 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 6 d3 c10 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 6 [0,6] t3 b4
  have b5 : a 11 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 1 d3 c11 (by decide +kernel)
  have t5 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 2 d3 c11 (by decide +kernel)
  have t6 : a 11 ∈ [0,3,4,5] := remove (a 11) 2 [0,2,3,4,5] t5 b6
  have b7 : a 11 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t7 : a 11 ∈ [0,4,5] := remove (a 11) 3 [0,3,4,5] t6 b7
  have b8 : a 11 ≠ 4 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 4 d3 c11 (by decide +kernel)
  have t8 : a 11 ∈ [0,5] := remove (a 11) 4 [0,4,5] t7 b8
  have b9 : a 11 ≠ 5 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 5 d3 c11 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 5 [0,5] t8 b9
  have b10 : a 4 ≠ 1 := exclude [0,1,8,9,16,17,24,25] (edge r12) (a 4) (a 5) 1 d5 c12 (by decide +kernel)
  have t10 : a 4 ∈ [0,4,5] := remove (a 4) 1 [0,1,4,5] d4 b10
  have b11 : a 4 ≠ 5 := exclude [0,1,8,9,16,17,24,25] (edge r12) (a 4) (a 5) 5 d5 c12 (by decide +kernel)
  have t11 : a 4 ∈ [0,4] := remove (a 4) 5 [0,4,5] t10 b11
  have b12 : a 5 ≠ 16 := exclude [0,4] (fun u v => edge r12 v u) (a 5) (a 4) 16 t11 c12 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,8,9,17,24,25] := remove (a 5) 16 [0,1,8,9,16,17,24,25] d5 b12
  have b13 : a 5 ≠ 17 := exclude [0,4] (fun u v => edge r12 v u) (a 5) (a 4) 17 t11 c12 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,8,9,24,25] := remove (a 5) 17 [0,1,8,9,17,24,25] t12 b13
  have b14 : a 5 ≠ 24 := exclude [0,4] (fun u v => edge r12 v u) (a 5) (a 4) 24 t11 c12 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,8,9,25] := remove (a 5) 24 [0,1,8,9,24,25] t13 b14
  have b15 : a 5 ≠ 25 := exclude [0,4] (fun u v => edge r12 v u) (a 5) (a 4) 25 t11 c12 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,8,9] := remove (a 5) 25 [0,1,8,9,25] t14 b15
  exact And.intro t4 (And.intro t9 (And.intro t11 (t15)))

theorem chunk5 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,4])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,8,9])
    (d13 : a 13 ∈ [0,1,2])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3])
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    : a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 5 ∈ [0,8] ∧ a 13 ∈ [0] ∧ a 15 ∈ [0,1] ∧ a 8 ∈ [0,1] ∧ a 9 ∈ [0,2,3] := by
  have b0 : a 4 ≠ 4 := exclude [0,1] (edge r13) (a 4) (a 6) 4 d6 c13 (by decide +kernel)
  have t0 : a 4 ∈ [0] := remove (a 4) 4 [0,4] d4 b0
  have b1 : a 6 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 6) (a 4) 1 t0 c13 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b1
  have b2 : a 12 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 1 t0 c14 (by decide +kernel)
  have t2 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b2
  have b3 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t0 c14 (by decide +kernel)
  have t3 : a 12 ∈ [0,3] := remove (a 12) 2 [0,2,3] t2 b3
  have b4 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t0 c14 (by decide +kernel)
  have t4 : a 12 ∈ [0] := remove (a 12) 3 [0,3] t3 b4
  have b5 : a 5 ≠ 1 := exclude [0,1,2] (edge r16) (a 5) (a 13) 1 d13 c16 (by decide +kernel)
  have t5 : a 5 ∈ [0,8,9] := remove (a 5) 1 [0,1,8,9] d5 b5
  have b6 : a 5 ≠ 9 := exclude [0,1,2] (edge r16) (a 5) (a 13) 9 d13 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0,8] := remove (a 5) 9 [0,8,9] t5 b6
  have b7 : a 13 ≠ 1 := exclude [0,8] (fun u v => edge r16 v u) (a 13) (a 5) 1 t6 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,2] := remove (a 13) 1 [0,1,2] d13 b7
  have b8 : a 13 ≠ 2 := exclude [0,8] (fun u v => edge r16 v u) (a 13) (a 5) 2 t6 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0] := remove (a 13) 2 [0,2] t7 b8
  have b9 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,3,4,5] := remove (a 15) 2 [0,1,2,3,4,5] d15 b9
  have b10 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t10 : a 15 ∈ [0,1,4,5] := remove (a 15) 3 [0,1,3,4,5] t9 b10
  have b11 : a 15 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 4 d7 c19 (by decide +kernel)
  have t11 : a 15 ∈ [0,1,5] := remove (a 15) 4 [0,1,4,5] t10 b11
  have b12 : a 15 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t12 : a 15 ∈ [0,1] := remove (a 15) 5 [0,1,5] t11 b12
  have b13 : a 8 ≠ 2 := exclude [0,1,2,3] (edge r20) (a 8) (a 9) 2 d9 c20 (by decide +kernel)
  have t13 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b13
  have b14 : a 8 ≠ 3 := exclude [0,1,2,3] (edge r20) (a 8) (a 9) 3 d9 c20 (by decide +kernel)
  have t14 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t13 b14
  have b15 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r20 v u) (a 9) (a 8) 1 t14 c20 (by decide +kernel)
  have t15 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b15
  exact And.intro t0 (And.intro t1 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t12 (And.intro t14 (t15)))))))

theorem chunk6 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,2,3])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d11 : a 11 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3,4,5])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,8])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    : a 9 ∈ [0] ∧ a 8 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 1 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r20 v u) (a 9) (a 8) 3 d8 c20 (by decide +kernel)
  have t0 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] d9 b0
  have b1 : a 8 ≠ 1 := exclude [0] (edge r22) (a 8) (a 12) 1 d12 c22 (by decide +kernel)
  have t1 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b1
  have b2 : a 9 ≠ 2 := exclude [0] (edge r23) (a 9) (a 11) 2 d11 c23 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 2 [0,2] t0 b2
  have b3 : a 14 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 10) 1 d10 c26 (by decide +kernel)
  have t3 : a 14 ∈ [0,2,3,4,5] := remove (a 14) 1 [0,1,2,3,4,5] d14 b3
  have b4 : a 14 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 10) 2 d10 c26 (by decide +kernel)
  have t4 : a 14 ∈ [0,3,4,5] := remove (a 14) 2 [0,2,3,4,5] t3 b4
  have b5 : a 14 ≠ 3 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 10) 3 d10 c26 (by decide +kernel)
  have t5 : a 14 ∈ [0,4,5] := remove (a 14) 3 [0,3,4,5] t4 b5
  have b6 : a 14 ≠ 4 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 10) 4 d10 c26 (by decide +kernel)
  have t6 : a 14 ∈ [0,5] := remove (a 14) 4 [0,4,5] t5 b6
  have b7 : a 14 ≠ 5 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 10) 5 d10 c26 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 5 [0,5] t6 b7
  have b8 : a 15 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 1 d11 c27 (by decide +kernel)
  have t8 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b8
  have b9 : a 1 ≠ 1 := exclude [0] (edge r4) (a 1) (a 3) 1 d3 c4 (by decide +kernel)
  have t9 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b9
  have b10 : a 5 ≠ 8 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 8 t9 c5 (by decide +kernel)
  have t10 : a 5 ∈ [0] := remove (a 5) 8 [0,8] d5 b10
  exact And.intro t2 (And.intro t1 (And.intro t7 (And.intro t8 (And.intro t9 (t10)))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6,7])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3])
    (start13 : a 13 ∈ [0,1,2])
    (start14 : a 14 ∈ [0,1,2,3,4,5])
    (start15 : a 15 ∈ [0,1,2,3,4,5])
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
  have group1 := chunk0 a start2 start0 start4 c1 c2
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a h3 start0 start5 start1 c2 c5
  rcases group4 with ⟨h5,h6⟩
  have group7 := chunk2 a h6 start1 start3 h2 c5 c7
  rcases group7 with ⟨h8,h9⟩
  have group10 := chunk3 a start6 h2 start10 start7 h9 c8 c9 c10
  rcases group10 with ⟨h11,h12,h13⟩
  have group14 := chunk4 a h13 h9 start11 h5 h8 c10 c11 c12
  rcases group14 with ⟨h15,h16,h17,h18⟩
  have group19 := chunk5 a h17 h11 start12 h18 start13 start15 h15 start8 start9 c13 c14 c16 c19 c20
  rcases group19 with ⟨h20,h21,h22,h23,h24,h25,h26,h27⟩
  have group28 := chunk6 a h27 h26 h22 h16 start14 h12 h25 start1 h9 h23 c4 c5 c20 c22 c23 c26 c27
  rcases group28 with ⟨h29,h30,h31,h32,h33,h34⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h33) (And.intro (forced (a 2) 0 h2) (And.intro (forced (a 3) 0 h9) (And.intro (forced (a 4) 0 h20) (And.intro (forced (a 5) 0 h34) (And.intro (forced (a 6) 0 h21) (And.intro (forced (a 7) 0 h15) (And.intro (forced (a 8) 0 h30) (And.intro (forced (a 9) 0 h29) (And.intro (forced (a 10) 0 h12) (And.intro (forced (a 11) 0 h16) (And.intro (forced (a 12) 0 h22) (And.intro (forced (a 13) 0 h24) (And.intro (forced (a 14) 0 h31) (forced (a 15) 0 h32)))))))))))))))
#print axioms cover
end PartitionCover205_109
