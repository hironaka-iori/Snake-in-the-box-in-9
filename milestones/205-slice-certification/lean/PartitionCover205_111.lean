import FiniteDomain205
namespace PartitionCover205_111
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[5]
def r2 : Array Nat := #[15]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[63]
def r5 : Array Nat := #[3]
def r6 : Array Nat := #[3]
def r7 : Array Nat := #[1,2,4,8,16,32]
def r8 : Array Nat := #[3,12,48,192,768,3072]
def r9 : Array Nat := #[1,1,0,0,0,0]
def r10 : Array Nat := #[1,2,4,8,16,32]
def r11 : Array Nat := #[1,1,0,0,0,0]
def r12 : Array Nat := #[1,1,0,0]
def r13 : Array Nat := #[2051,560,163,58]
def r14 : Array Nat := #[1,0,0,0]
def r15 : Array Nat := #[5,0]
def r16 : Array Nat := #[3,12]
def r17 : Array Nat := #[3,0,3,0,12,0,12,0,48,0,48,0]
def r18 : Array Nat := #[1,0,3,0,0,0,0,0,0,0,0,0]
def r19 : Array Nat := #[1,1,1,1,9,9]
def r20 : Array Nat := #[1,2,4,8]
def r21 : Array Nat := #[1,2,4,8]
def r22 : Array Nat := #[1,2,4,8]
def r23 : Array Nat := #[1,2,4,8]
def r24 : Array Nat := #[1,2,4,8]
def r25 : Array Nat := #[1,2,4,8]
def r26 : Array Nat := #[1,2,4,8]
def r27 : Array Nat := #[1,2,4,8]
def r28 : Array Nat := #[3,3,12,12]
def r29 : Array Nat := #[1,2,4,8]
def r30 : Array Nat := #[1,2,4,8]
def r31 : Array Nat := #[1,2,4,8]
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0])
    (d3 : a 3 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    : a 2 ∈ [0,2] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0,1] ∧ a 3 ∈ [0,2] ∧ a 6 ∈ [0,1,4,5,7,8,9,10,11] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3,4,5] := remove (a 2) 1 [0,1,2,3,4,5] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2,4,5] := remove (a 2) 3 [0,2,3,4,5] t0 b1
  have b2 : a 2 ≠ 4 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 4 d0 c1 (by decide +kernel)
  have t2 : a 2 ∈ [0,2,5] := remove (a 2) 4 [0,2,4,5] t1 b2
  have b3 : a 2 ≠ 5 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 5 d0 c1 (by decide +kernel)
  have t3 : a 2 ∈ [0,2] := remove (a 2) 5 [0,2,5] t2 b3
  have b4 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b4
  have b5 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,3] := remove (a 8) 2 [0,2,3] t4 b5
  have b6 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t6 : a 8 ∈ [0] := remove (a 8) 3 [0,3] t5 b6
  have b7 : a 9 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 2 d1 c6 (by decide +kernel)
  have t7 : a 9 ∈ [0,1,3] := remove (a 9) 2 [0,1,2,3] d9 b7
  have b8 : a 9 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 3 d1 c6 (by decide +kernel)
  have t8 : a 9 ∈ [0,1] := remove (a 9) 3 [0,1,3] t7 b8
  have b9 : a 3 ≠ 1 := exclude [0,2] (fun u v => edge r7 v u) (a 3) (a 2) 1 t3 c7 (by decide +kernel)
  have t9 : a 3 ∈ [0,2,3,4,5] := remove (a 3) 1 [0,1,2,3,4,5] d3 b9
  have b10 : a 3 ≠ 3 := exclude [0,2] (fun u v => edge r7 v u) (a 3) (a 2) 3 t3 c7 (by decide +kernel)
  have t10 : a 3 ∈ [0,2,4,5] := remove (a 3) 3 [0,2,3,4,5] t9 b10
  have b11 : a 3 ≠ 4 := exclude [0,2] (fun u v => edge r7 v u) (a 3) (a 2) 4 t3 c7 (by decide +kernel)
  have t11 : a 3 ∈ [0,2,5] := remove (a 3) 4 [0,2,4,5] t10 b11
  have b12 : a 3 ≠ 5 := exclude [0,2] (fun u v => edge r7 v u) (a 3) (a 2) 5 t3 c7 (by decide +kernel)
  have t12 : a 3 ∈ [0,2] := remove (a 3) 5 [0,2,5] t11 b12
  have b13 : a 6 ≠ 2 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 2 t3 c8 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 6) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d6 b13
  have b14 : a 6 ≠ 3 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 3 t3 c8 (by decide +kernel)
  have t14 : a 6 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 6) 3 [0,1,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 6 ≠ 6 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 6 t3 c8 (by decide +kernel)
  have t15 : a 6 ∈ [0,1,4,5,7,8,9,10,11] := remove (a 6) 6 [0,1,4,5,6,7,8,9,10,11] t14 b15
  exact And.intro t3 (And.intro t6 (And.intro t8 (And.intro t12 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,4,5,7,8,9,10,11])
    (d2 : a 2 ∈ [0,2])
    (d10 : a 10 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,2])
    (d11 : a 11 ∈ [0,1,2,3])
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    : a 6 ∈ [0,1,4,5] ∧ a 2 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0,2] ∧ a 3 ∈ [0] ∧ a 11 ∈ [0,3] := by
  have b0 : a 6 ≠ 7 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 7 d2 c8 (by decide +kernel)
  have t0 : a 6 ∈ [0,1,4,5,8,9,10,11] := remove (a 6) 7 [0,1,4,5,7,8,9,10,11] d6 b0
  have b1 : a 6 ≠ 8 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 8 d2 c8 (by decide +kernel)
  have t1 : a 6 ∈ [0,1,4,5,9,10,11] := remove (a 6) 8 [0,1,4,5,8,9,10,11] t0 b1
  have b2 : a 6 ≠ 9 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 9 d2 c8 (by decide +kernel)
  have t2 : a 6 ∈ [0,1,4,5,10,11] := remove (a 6) 9 [0,1,4,5,9,10,11] t1 b2
  have b3 : a 6 ≠ 10 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 10 d2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0,1,4,5,11] := remove (a 6) 10 [0,1,4,5,10,11] t2 b3
  have b4 : a 6 ≠ 11 := exclude [0,2] (fun u v => edge r8 v u) (a 6) (a 2) 11 d2 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0,1,4,5] := remove (a 6) 11 [0,1,4,5,11] t3 b4
  have b5 : a 2 ≠ 2 := exclude [0,1,2,3] (edge r9) (a 2) (a 10) 2 d10 c9 (by decide +kernel)
  have t5 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b5
  have b6 : a 10 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 1 t5 c9 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b6
  have b7 : a 10 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 2 t5 c9 (by decide +kernel)
  have t7 : a 10 ∈ [0,3] := remove (a 10) 2 [0,2,3] t6 b7
  have b8 : a 10 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 3 t5 c9 (by decide +kernel)
  have t8 : a 10 ∈ [0] := remove (a 10) 3 [0,3] t7 b8
  have b9 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 1 d3 c10 (by decide +kernel)
  have t9 : a 7 ∈ [0,2,3,4,5] := remove (a 7) 1 [0,1,2,3,4,5] d7 b9
  have b10 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 3 d3 c10 (by decide +kernel)
  have t10 : a 7 ∈ [0,2,4,5] := remove (a 7) 3 [0,2,3,4,5] t9 b10
  have b11 : a 7 ≠ 4 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 4 d3 c10 (by decide +kernel)
  have t11 : a 7 ∈ [0,2,5] := remove (a 7) 4 [0,2,4,5] t10 b11
  have b12 : a 7 ≠ 5 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 5 d3 c10 (by decide +kernel)
  have t12 : a 7 ∈ [0,2] := remove (a 7) 5 [0,2,5] t11 b12
  have b13 : a 3 ≠ 2 := exclude [0,1,2,3] (edge r11) (a 3) (a 11) 2 d11 c11 (by decide +kernel)
  have t13 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b13
  have b14 : a 11 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 1 t13 c11 (by decide +kernel)
  have t14 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b14
  have b15 : a 11 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 2 t13 c11 (by decide +kernel)
  have t15 : a 11 ∈ [0,3] := remove (a 11) 2 [0,2,3] t14 b15
  exact And.intro t4 (And.intro t5 (And.intro t8 (And.intro t12 (And.intro t13 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,3])
    (d3 : a 3 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,4,5])
    (d7 : a 7 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,2,3])
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    : a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 12 ∈ [0] ∧ a 13 ∈ [0,1] ∧ a 6 ∈ [0] ∧ a 14 ∈ [0] := by
  have b0 : a 11 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t0 : a 11 ∈ [0] := remove (a 11) 3 [0,3] d11 b0
  have b1 : a 4 ≠ 2 := exclude [0,1] (edge r12) (a 4) (a 5) 2 d5 c12 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,3] := remove (a 4) 2 [0,1,2,3] d4 b1
  have b2 : a 4 ≠ 3 := exclude [0,1] (edge r12) (a 4) (a 5) 3 d5 c12 (by decide +kernel)
  have t2 : a 4 ∈ [0,1] := remove (a 4) 3 [0,1,3] t1 b2
  have b3 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 1 t2 c12 (by decide +kernel)
  have t3 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b3
  have b4 : a 4 ≠ 1 := exclude [0,1,2,3] (edge r14) (a 4) (a 12) 1 d12 c14 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 1 [0,1] t2 b4
  have b5 : a 12 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 1 t4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b5
  have b6 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t4 c14 (by decide +kernel)
  have t6 : a 12 ∈ [0,3] := remove (a 12) 2 [0,2,3] t5 b6
  have b7 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t4 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0] := remove (a 12) 3 [0,3] t6 b7
  have b8 : a 13 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 2 t3 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,3] := remove (a 13) 2 [0,1,2,3] d13 b8
  have b9 : a 13 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 3 t3 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,1] := remove (a 13) 3 [0,1,3] t8 b9
  have b10 : a 6 ≠ 1 := exclude [0,2] (edge r17) (a 6) (a 7) 1 d7 c17 (by decide +kernel)
  have t10 : a 6 ∈ [0,4,5] := remove (a 6) 1 [0,1,4,5] d6 b10
  have b11 : a 6 ≠ 5 := exclude [0,2] (edge r17) (a 6) (a 7) 5 d7 c17 (by decide +kernel)
  have t11 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t10 b11
  have b12 : a 6 ≠ 4 := exclude [0,1,2,3] (edge r18) (a 6) (a 14) 4 d14 c18 (by decide +kernel)
  have t12 : a 6 ∈ [0] := remove (a 6) 4 [0,4] t11 b12
  have b13 : a 14 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 1 t12 c18 (by decide +kernel)
  have t13 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b13
  have b14 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 t12 c18 (by decide +kernel)
  have t14 : a 14 ∈ [0,3] := remove (a 14) 2 [0,2,3] t13 b14
  have b15 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 t12 c18 (by decide +kernel)
  have t15 : a 14 ∈ [0] := remove (a 14) 3 [0,3] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t3 (And.intro t7 (And.intro t9 (And.intro t12 (t15))))))

theorem chunk3 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d13 : a 13 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (c10 : edge r10 (a 3) (a 7)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    : a 15 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 7 ∈ [0] := by
  have b0 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 1 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b0
  have b1 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,3] := remove (a 15) 2 [0,2,3] t0 b1
  have b2 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0] := remove (a 15) 3 [0,3] t1 b2
  have b3 : a 9 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 9) (a 8) 1 d8 c20 (by decide +kernel)
  have t3 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b3
  have b4 : a 13 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 13) (a 9) 1 t3 c24 (by decide +kernel)
  have t4 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b4
  have b5 : a 7 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 2 d3 c10 (by decide +kernel)
  have t5 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b5
  exact And.intro t2 (And.intro t3 (And.intro t4 (t5)))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2,3,4,5])
    (start3 : a 3 ∈ [0,1,2,3,4,5])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1,2,3,4,5])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1,2,3])
    (start13 : a 13 ∈ [0,1,2,3])
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
  have group1 := chunk0 a start2 start0 start8 start9 start1 start3 start6 c1 c3 c6 c7 c8
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  have group7 := chunk1 a h6 h2 start10 start7 h5 start11 c8 c9 c10 c11
  rcases group7 with ⟨h8,h9,h10,h11,h12,h13⟩
  have group14 := chunk2 a h13 h12 start4 start5 start12 start13 h8 h11 start14 c11 c12 c14 c16 c17 c18
  rcases group14 with ⟨h15,h16,h17,h18,h19,h20,h21⟩
  have group22 := chunk3 a start15 h11 h4 h3 h19 h12 c10 c19 c20 c24
  rcases group22 with ⟨h23,h24,h25,h26⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h9) (And.intro (forced (a 3) 0 h12) (And.intro (forced (a 4) 0 h16) (And.intro (forced (a 5) 0 h17) (And.intro (forced (a 6) 0 h20) (And.intro (forced (a 7) 0 h26) (And.intro (forced (a 8) 0 h3) (And.intro (forced (a 9) 0 h24) (And.intro (forced (a 10) 0 h10) (And.intro (forced (a 11) 0 h15) (And.intro (forced (a 12) 0 h18) (And.intro (forced (a 13) 0 h25) (And.intro (forced (a 14) 0 h21) (forced (a 15) 0 h23)))))))))))))))
#print axioms cover
end PartitionCover205_111
