import FiniteDomain205
namespace PartitionCover205_156
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[127]
def r1 : Array Nat := #[3]
def r2 : Array Nat := #[63]
def r3 : Array Nat := #[15]
def r4 : Array Nat := #[1,2,4,8,16,32,64]
def r5 : Array Nat := #[1,0,0,0,0,0,0]
def r6 : Array Nat := #[3,12,12,3,48,192,768]
def r7 : Array Nat := #[1,1]
def r8 : Array Nat := #[3,3]
def r9 : Array Nat := #[1,2]
def r10 : Array Nat := #[1,2,4,8,16,32,64]
def r11 : Array Nat := #[1,0,0,0,2,0,0]
def r12 : Array Nat := #[3,12,48,192,768,3072]
def r13 : Array Nat := #[3,0,3,0,0,0]
def r14 : Array Nat := #[1,0,16,0,0,0]
def r15 : Array Nat := #[1,1,0,0,0,0,0,0,0,0,0,0]
def r16 : Array Nat := #[3,3,12,12,48,48,192,192,768,768,3072,3072]
def r17 : Array Nat := #[1,0]
def r18 : Array Nat := #[3,12]
def r19 : Array Nat := #[1,0,0,0,0,0,0]
def r20 : Array Nat := #[3,3,3,3]
def r21 : Array Nat := #[1,1,2,2]
def r22 : Array Nat := #[51,0,51,0]
def r23 : Array Nat := #[3,0,0,0,0,0,0,0,0,0]
def r24 : Array Nat := #[1297,0,0,0,0,2176,0,34,0,0]
def r25 : Array Nat := #[3,12]
def r26 : Array Nat := #[3,12]
def r27 : Array Nat := #[1,0,4,0]
def r28 : Array Nat := #[1,0,32,0,16,0,2,0]
def r29 : Array Nat := #[1,1,2,2,4,4,8,8]
def r30 : Array Nat := #[5,5,0,0,5,5,0,0,0,0,0,0]
def r31 : Array Nat := #[1,2,4,8]
theorem chunk0 (a : Nat → Nat)
    (d1 : a 1 ∈ [0,1,2,3,4,5,6])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c5 : edge r5 (a 1) (a 5)=true)
    : a 1 ∈ [0] ∧ a 5 ∈ [0,11] := by
  have b0 : a 1 ≠ 1 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r5) (a 1) (a 5) 1 d5 c5 (by decide +kernel)
  have t0 : a 1 ∈ [0,2,3,4,5,6] := remove (a 1) 1 [0,1,2,3,4,5,6] d1 b0
  have b1 : a 1 ≠ 2 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r5) (a 1) (a 5) 2 d5 c5 (by decide +kernel)
  have t1 : a 1 ∈ [0,3,4,5,6] := remove (a 1) 2 [0,2,3,4,5,6] t0 b1
  have b2 : a 1 ≠ 3 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r5) (a 1) (a 5) 3 d5 c5 (by decide +kernel)
  have t2 : a 1 ∈ [0,4,5,6] := remove (a 1) 3 [0,3,4,5,6] t1 b2
  have b3 : a 1 ≠ 4 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r5) (a 1) (a 5) 4 d5 c5 (by decide +kernel)
  have t3 : a 1 ∈ [0,5,6] := remove (a 1) 4 [0,4,5,6] t2 b3
  have b4 : a 1 ≠ 5 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r5) (a 1) (a 5) 5 d5 c5 (by decide +kernel)
  have t4 : a 1 ∈ [0,6] := remove (a 1) 5 [0,5,6] t3 b4
  have b5 : a 1 ≠ 6 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r5) (a 1) (a 5) 6 d5 c5 (by decide +kernel)
  have t5 : a 1 ∈ [0] := remove (a 1) 6 [0,6] t4 b5
  have b6 : a 5 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 1 t5 c5 (by decide +kernel)
  have t6 : a 5 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d5 b6
  have b7 : a 5 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 2 t5 c5 (by decide +kernel)
  have t7 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 5) 2 [0,2,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 5 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 3 t5 c5 (by decide +kernel)
  have t8 : a 5 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 5) 3 [0,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 5 ≠ 4 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 4 t5 c5 (by decide +kernel)
  have t9 : a 5 ∈ [0,5,6,7,8,9,10,11] := remove (a 5) 4 [0,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 5 ≠ 5 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 5 t5 c5 (by decide +kernel)
  have t10 : a 5 ∈ [0,6,7,8,9,10,11] := remove (a 5) 5 [0,5,6,7,8,9,10,11] t9 b10
  have b11 : a 5 ≠ 6 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 6 t5 c5 (by decide +kernel)
  have t11 : a 5 ∈ [0,7,8,9,10,11] := remove (a 5) 6 [0,6,7,8,9,10,11] t10 b11
  have b12 : a 5 ≠ 7 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 7 t5 c5 (by decide +kernel)
  have t12 : a 5 ∈ [0,8,9,10,11] := remove (a 5) 7 [0,7,8,9,10,11] t11 b12
  have b13 : a 5 ≠ 8 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 8 t5 c5 (by decide +kernel)
  have t13 : a 5 ∈ [0,9,10,11] := remove (a 5) 8 [0,8,9,10,11] t12 b13
  have b14 : a 5 ≠ 9 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 9 t5 c5 (by decide +kernel)
  have t14 : a 5 ∈ [0,10,11] := remove (a 5) 9 [0,9,10,11] t13 b14
  have b15 : a 5 ≠ 10 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 10 t5 c5 (by decide +kernel)
  have t15 : a 5 ∈ [0,11] := remove (a 5) 10 [0,10,11] t14 b15
  exact And.intro t5 (t15)

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,11])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9])
    (d3 : a 3 ∈ [0,1,2,3,4,5,6])
    (d2 : a 2 ∈ [0,1])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6])
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    : a 5 ∈ [0] ∧ a 9 ∈ [0,1] ∧ a 3 ∈ [0] ∧ a 7 ∈ [0,2,3,4,5,6] := by
  have b0 : a 5 ≠ 11 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 11 d1 c5 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 11 [0,11] d5 b0
  have b1 : a 9 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 2 d1 c6 (by decide +kernel)
  have t1 : a 9 ∈ [0,1,3,4,5,6,7,8,9] := remove (a 9) 2 [0,1,2,3,4,5,6,7,8,9] d9 b1
  have b2 : a 9 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 3 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [0,1,4,5,6,7,8,9] := remove (a 9) 3 [0,1,3,4,5,6,7,8,9] t1 b2
  have b3 : a 9 ≠ 4 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 4 d1 c6 (by decide +kernel)
  have t3 : a 9 ∈ [0,1,5,6,7,8,9] := remove (a 9) 4 [0,1,4,5,6,7,8,9] t2 b3
  have b4 : a 9 ≠ 5 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 5 d1 c6 (by decide +kernel)
  have t4 : a 9 ∈ [0,1,6,7,8,9] := remove (a 9) 5 [0,1,5,6,7,8,9] t3 b4
  have b5 : a 9 ≠ 6 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 6 d1 c6 (by decide +kernel)
  have t5 : a 9 ∈ [0,1,7,8,9] := remove (a 9) 6 [0,1,6,7,8,9] t4 b5
  have b6 : a 9 ≠ 7 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 7 d1 c6 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,8,9] := remove (a 9) 7 [0,1,7,8,9] t5 b6
  have b7 : a 9 ≠ 8 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 8 d1 c6 (by decide +kernel)
  have t7 : a 9 ∈ [0,1,9] := remove (a 9) 8 [0,1,8,9] t6 b7
  have b8 : a 9 ≠ 9 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 9 d1 c6 (by decide +kernel)
  have t8 : a 9 ∈ [0,1] := remove (a 9) 9 [0,1,9] t7 b8
  have b9 : a 3 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 3) (a 2) 1 d2 c7 (by decide +kernel)
  have t9 : a 3 ∈ [0,2,3,4,5,6] := remove (a 3) 1 [0,1,2,3,4,5,6] d3 b9
  have b10 : a 3 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 3) (a 2) 2 d2 c7 (by decide +kernel)
  have t10 : a 3 ∈ [0,3,4,5,6] := remove (a 3) 2 [0,2,3,4,5,6] t9 b10
  have b11 : a 3 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 3) (a 2) 3 d2 c7 (by decide +kernel)
  have t11 : a 3 ∈ [0,4,5,6] := remove (a 3) 3 [0,3,4,5,6] t10 b11
  have b12 : a 3 ≠ 4 := exclude [0,1] (fun u v => edge r7 v u) (a 3) (a 2) 4 d2 c7 (by decide +kernel)
  have t12 : a 3 ∈ [0,5,6] := remove (a 3) 4 [0,4,5,6] t11 b12
  have b13 : a 3 ≠ 5 := exclude [0,1] (fun u v => edge r7 v u) (a 3) (a 2) 5 d2 c7 (by decide +kernel)
  have t13 : a 3 ∈ [0,6] := remove (a 3) 5 [0,5,6] t12 b13
  have b14 : a 3 ≠ 6 := exclude [0,1] (fun u v => edge r7 v u) (a 3) (a 2) 6 d2 c7 (by decide +kernel)
  have t14 : a 3 ∈ [0] := remove (a 3) 6 [0,6] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 1 t14 c10 (by decide +kernel)
  have t15 : a 7 ∈ [0,2,3,4,5,6] := remove (a 7) 1 [0,1,2,3,4,5,6] d7 b15
  exact And.intro t0 (And.intro t8 (And.intro t14 (t15)))

theorem chunk2 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2,3,4,5,6])
    (d3 : a 3 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0,4,5,6,7] := by
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
  have t5 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b5
  have b6 : a 11 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 2 d3 c11 (by decide +kernel)
  have t6 : a 11 ∈ [0,3] := remove (a 11) 2 [0,2,3] t5 b6
  have b7 : a 11 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t7 : a 11 ∈ [0] := remove (a 11) 3 [0,3] t6 b7
  have b8 : a 4 ≠ 1 := exclude [0] (edge r12) (a 4) (a 5) 1 d5 c12 (by decide +kernel)
  have t8 : a 4 ∈ [0,2,3,4,5] := remove (a 4) 1 [0,1,2,3,4,5] d4 b8
  have b9 : a 4 ≠ 2 := exclude [0] (edge r12) (a 4) (a 5) 2 d5 c12 (by decide +kernel)
  have t9 : a 4 ∈ [0,3,4,5] := remove (a 4) 2 [0,2,3,4,5] t8 b9
  have b10 : a 4 ≠ 3 := exclude [0] (edge r12) (a 4) (a 5) 3 d5 c12 (by decide +kernel)
  have t10 : a 4 ∈ [0,4,5] := remove (a 4) 3 [0,3,4,5] t9 b10
  have b11 : a 4 ≠ 4 := exclude [0] (edge r12) (a 4) (a 5) 4 d5 c12 (by decide +kernel)
  have t11 : a 4 ∈ [0,5] := remove (a 4) 4 [0,4,5] t10 b11
  have b12 : a 4 ≠ 5 := exclude [0] (edge r12) (a 4) (a 5) 5 d5 c12 (by decide +kernel)
  have t12 : a 4 ∈ [0] := remove (a 4) 5 [0,5] t11 b12
  have b13 : a 12 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 1 t12 c14 (by decide +kernel)
  have t13 : a 12 ∈ [0,2,3,4,5,6,7] := remove (a 12) 1 [0,1,2,3,4,5,6,7] d12 b13
  have b14 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t12 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,3,4,5,6,7] := remove (a 12) 2 [0,2,3,4,5,6,7] t13 b14
  have b15 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t12 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,4,5,6,7] := remove (a 12) 3 [0,3,4,5,6,7] t14 b15
  exact And.intro t4 (And.intro t7 (And.intro t12 (t15)))

theorem chunk3 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,4,5,6,7])
    (d4 : a 4 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3])
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    : a 12 ∈ [0] ∧ a 13 ∈ [0,1] ∧ a 6 ∈ [0] ∧ a 14 ∈ [0,1,3] := by
  have b0 : a 12 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 4 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,5,6,7] := remove (a 12) 4 [0,4,5,6,7] d12 b0
  have b1 : a 12 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 5 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,6,7] := remove (a 12) 5 [0,5,6,7] t0 b1
  have b2 : a 12 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 6 d4 c14 (by decide +kernel)
  have t2 : a 12 ∈ [0,7] := remove (a 12) 6 [0,6,7] t1 b2
  have b3 : a 12 ≠ 7 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 7 d4 c14 (by decide +kernel)
  have t3 : a 12 ∈ [0] := remove (a 12) 7 [0,7] t2 b3
  have b4 : a 13 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 13) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d13 b4
  have b5 : a 13 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 13) 3 [0,1,3,4,5,6,7,8,9,10,11] t4 b5
  have b6 : a 13 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 13) 4 [0,1,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 13 ≠ 5 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,6,7,8,9,10,11] := remove (a 13) 5 [0,1,5,6,7,8,9,10,11] t6 b7
  have b8 : a 13 ≠ 6 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,7,8,9,10,11] := remove (a 13) 6 [0,1,6,7,8,9,10,11] t7 b8
  have b9 : a 13 ≠ 7 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,8,9,10,11] := remove (a 13) 7 [0,1,7,8,9,10,11] t8 b9
  have b10 : a 13 ≠ 8 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 8 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,9,10,11] := remove (a 13) 8 [0,1,8,9,10,11] t9 b10
  have b11 : a 13 ≠ 9 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 9 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,10,11] := remove (a 13) 9 [0,1,9,10,11] t10 b11
  have b12 : a 13 ≠ 10 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 10 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,11] := remove (a 13) 10 [0,1,10,11] t11 b12
  have b13 : a 13 ≠ 11 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 11 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,1] := remove (a 13) 11 [0,1,11] t12 b13
  have b14 : a 6 ≠ 1 := exclude [0] (edge r17) (a 6) (a 7) 1 d7 c17 (by decide +kernel)
  have t14 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b14
  have b15 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 t14 c18 (by decide +kernel)
  have t15 : a 14 ∈ [0,1,3] := remove (a 14) 2 [0,1,2,3] d14 b15
  exact And.intro t3 (And.intro t13 (And.intro t14 (t15)))

theorem chunk4 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,3])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0])
    (d9 : a 9 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d13 : a 13 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (c9 : edge r9 (a 2) (a 10)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    (c29 : edge r29 (a 12) (a 14)=true)
    : a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 10 ∈ [0] ∧ a 2 ∈ [0] := by
  have b0 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 d6 c18 (by decide +kernel)
  have t0 : a 14 ∈ [0,1] := remove (a 14) 3 [0,1,3] d14 b0
  have b1 : a 15 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 1 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b1
  have b2 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,3] := remove (a 15) 2 [0,2,3] t1 b2
  have b3 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0] := remove (a 15) 3 [0,3] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (edge r22) (a 8) (a 12) 1 d12 c22 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b4
  have b5 : a 8 ≠ 3 := exclude [0] (edge r22) (a 8) (a 12) 3 d12 c22 (by decide +kernel)
  have t5 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t4 b5
  have b6 : a 9 ≠ 1 := exclude [0] (edge r23) (a 9) (a 11) 1 d11 c23 (by decide +kernel)
  have t6 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b6
  have b7 : a 13 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 13) (a 9) 1 t6 c24 (by decide +kernel)
  have t7 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b7
  have b8 : a 10 ≠ 1 := exclude [0] (edge r25) (a 10) (a 11) 1 d11 c25 (by decide +kernel)
  have t8 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b8
  have b9 : a 14 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 14) (a 12) 1 d12 c29 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 1 [0,1] t0 b9
  have b10 : a 2 ≠ 1 := exclude [0] (edge r9) (a 2) (a 10) 1 t8 c9 (by decide +kernel)
  have t10 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b10
  have b11 : a 8 ≠ 2 := exclude [0] (edge r21) (a 8) (a 10) 2 t8 c21 (by decide +kernel)
  have t11 : a 8 ∈ [0] := remove (a 8) 2 [0,2] t5 b11
  exact And.intro t9 (And.intro t3 (And.intro t11 (And.intro t6 (And.intro t7 (And.intro t8 (t10))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2,3,4,5,6])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1,2,3,4,5,6])
    (start4 : a 4 ∈ [0,1,2,3,4,5])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7,8,9])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1,2,3])
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
  have group1 := chunk0 a start1 start5 c5
  rcases group1 with ⟨h2,h3⟩
  have group4 := chunk1 a h3 h2 start9 start3 start2 start7 c5 c6 c7 c10
  rcases group4 with ⟨h5,h6,h7,h8⟩
  have group9 := chunk2 a h8 h7 start11 start4 h5 start12 c10 c11 c12 c14
  rcases group9 with ⟨h10,h11,h12,h13⟩
  have group14 := chunk3 a h13 h12 start13 h5 start6 h10 start14 c14 c16 c17 c18
  rcases group14 with ⟨h15,h16,h17,h18⟩
  have group19 := chunk4 a h18 h17 start15 h10 start8 h15 h6 h11 h16 start10 start2 c9 c18 c19 c21 c22 c23 c24 c25 c29
  rcases group19 with ⟨h20,h21,h22,h23,h24,h25,h26⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h2) (And.intro (forced (a 2) 0 h26) (And.intro (forced (a 3) 0 h7) (And.intro (forced (a 4) 0 h12) (And.intro (forced (a 5) 0 h5) (And.intro (forced (a 6) 0 h17) (And.intro (forced (a 7) 0 h10) (And.intro (forced (a 8) 0 h22) (And.intro (forced (a 9) 0 h23) (And.intro (forced (a 10) 0 h25) (And.intro (forced (a 11) 0 h11) (And.intro (forced (a 12) 0 h15) (And.intro (forced (a 13) 0 h24) (And.intro (forced (a 14) 0 h20) (forced (a 15) 0 h21)))))))))))))))
#print axioms cover
end PartitionCover205_156
