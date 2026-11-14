import FiniteDomain205
namespace PartitionCover205_147
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[15]
def r1 : Array Nat := #[15]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[5]
def r4 : Array Nat := #[1,2,4,8]
def r5 : Array Nat := #[7,56,448,3584]
def r6 : Array Nat := #[5,5,5,5]
def r7 : Array Nat := #[1,2,1,2]
def r8 : Array Nat := #[1,2,4,8]
def r9 : Array Nat := #[1,4,1,4]
def r10 : Array Nat := #[3,3,12,12]
def r11 : Array Nat := #[5,5,0,0]
def r12 : Array Nat := #[1,8]
def r13 : Array Nat := #[1,2]
def r14 : Array Nat := #[3,12]
def r15 : Array Nat := #[3,0,0,3,0,0,12,0,0,12,0,0]
def r16 : Array Nat := #[5,0,5,5,0,5,0,0,0,0,0,0]
def r17 : Array Nat := #[5,10,0,0]
def r18 : Array Nat := #[1,4,0,0]
def r19 : Array Nat := #[13,7,0,0]
def r20 : Array Nat := #[5,2,5,8]
def r21 : Array Nat := #[1,2,4,8]
def r22 : Array Nat := #[1,2,4,8]
def r23 : Array Nat := #[1,2,4,8]
def r24 : Array Nat := #[1,2,4,8]
def r25 : Array Nat := #[5,2,5,8]
def r26 : Array Nat := #[1,2,4,8]
def r27 : Array Nat := #[1,2,4,8]
def r28 : Array Nat := #[13,2,7,8]
def r29 : Array Nat := #[1,10,4,10]
def r30 : Array Nat := #[1,2,4,8]
def r31 : Array Nat := #[1,2,4,8]
theorem chunk0 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d4 : a 4 ∈ [0,1])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    : a 8 ∈ [0,2] ∧ a 9 ∈ [0,2] ∧ a 3 ∈ [0,1] ∧ a 10 ∈ [0,2] ∧ a 7 ∈ [0,1] ∧ a 11 ∈ [0,2] ∧ a 5 ∈ [0,3,6,7,8,9,10,11] := by
  have b0 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b0
  have b1 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t0 b1
  have b2 : a 9 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r6 v u) (a 9) (a 1) 1 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b2
  have b3 : a 9 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r6 v u) (a 9) (a 1) 3 d1 c6 (by decide +kernel)
  have t3 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t2 b3
  have b4 : a 3 ≠ 2 := exclude [0,1,2,3] (fun u v => edge r7 v u) (a 3) (a 2) 2 d2 c7 (by decide +kernel)
  have t4 : a 3 ∈ [0,1,3] := remove (a 3) 2 [0,1,2,3] d3 b4
  have b5 : a 3 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r7 v u) (a 3) (a 2) 3 d2 c7 (by decide +kernel)
  have t5 : a 3 ∈ [0,1] := remove (a 3) 3 [0,1,3] t4 b5
  have b6 : a 10 ≠ 1 := exclude [0,1,2,3] (fun u v => edge r9 v u) (a 10) (a 2) 1 d2 c9 (by decide +kernel)
  have t6 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b6
  have b7 : a 10 ≠ 3 := exclude [0,1,2,3] (fun u v => edge r9 v u) (a 10) (a 2) 3 d2 c9 (by decide +kernel)
  have t7 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t6 b7
  have b8 : a 7 ≠ 2 := exclude [0,1] (fun u v => edge r10 v u) (a 7) (a 3) 2 t5 c10 (by decide +kernel)
  have t8 : a 7 ∈ [0,1,3] := remove (a 7) 2 [0,1,2,3] d7 b8
  have b9 : a 7 ≠ 3 := exclude [0,1] (fun u v => edge r10 v u) (a 7) (a 3) 3 t5 c10 (by decide +kernel)
  have t9 : a 7 ∈ [0,1] := remove (a 7) 3 [0,1,3] t8 b9
  have b10 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 1 t5 c11 (by decide +kernel)
  have t10 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b10
  have b11 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 3 t5 c11 (by decide +kernel)
  have t11 : a 11 ∈ [0,2] := remove (a 11) 3 [0,2,3] t10 b11
  have b12 : a 5 ≠ 1 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 1 d4 c12 (by decide +kernel)
  have t12 : a 5 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 5) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d5 b12
  have b13 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 2 d4 c12 (by decide +kernel)
  have t13 : a 5 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 5) 2 [0,2,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 4 d4 c12 (by decide +kernel)
  have t14 : a 5 ∈ [0,3,5,6,7,8,9,10,11] := remove (a 5) 4 [0,3,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 5 d4 c12 (by decide +kernel)
  have t15 : a 5 ∈ [0,3,6,7,8,9,10,11] := remove (a 5) 5 [0,3,5,6,7,8,9,10,11] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,3,6,7,8,9,10,11])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,2])
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    : a 5 ∈ [0,3] ∧ a 6 ∈ [0,1] ∧ a 13 ∈ [0,2] ∧ a 14 ∈ [0,2] ∧ a 12 ∈ [0,2] ∧ a 15 ∈ [0,2] := by
  have b0 : a 5 ≠ 6 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 6 d4 c12 (by decide +kernel)
  have t0 : a 5 ∈ [0,3,7,8,9,10,11] := remove (a 5) 6 [0,3,6,7,8,9,10,11] d5 b0
  have b1 : a 5 ≠ 7 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 7 d4 c12 (by decide +kernel)
  have t1 : a 5 ∈ [0,3,8,9,10,11] := remove (a 5) 7 [0,3,7,8,9,10,11] t0 b1
  have b2 : a 5 ≠ 8 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 8 d4 c12 (by decide +kernel)
  have t2 : a 5 ∈ [0,3,9,10,11] := remove (a 5) 8 [0,3,8,9,10,11] t1 b2
  have b3 : a 5 ≠ 9 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 9 d4 c12 (by decide +kernel)
  have t3 : a 5 ∈ [0,3,10,11] := remove (a 5) 9 [0,3,9,10,11] t2 b3
  have b4 : a 5 ≠ 10 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 10 d4 c12 (by decide +kernel)
  have t4 : a 5 ∈ [0,3,11] := remove (a 5) 10 [0,3,10,11] t3 b4
  have b5 : a 5 ≠ 11 := exclude [0,1] (fun u v => edge r12 v u) (a 5) (a 4) 11 d4 c12 (by decide +kernel)
  have t5 : a 5 ∈ [0,3] := remove (a 5) 11 [0,3,11] t4 b5
  have b6 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 6) (a 4) 2 d4 c13 (by decide +kernel)
  have t6 : a 6 ∈ [0,1,3] := remove (a 6) 2 [0,1,2,3] d6 b6
  have b7 : a 6 ≠ 3 := exclude [0,1] (fun u v => edge r13 v u) (a 6) (a 4) 3 d4 c13 (by decide +kernel)
  have t7 : a 6 ∈ [0,1] := remove (a 6) 3 [0,1,3] t6 b7
  have b8 : a 13 ≠ 1 := exclude [0,3] (fun u v => edge r16 v u) (a 13) (a 5) 1 t5 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b8
  have b9 : a 13 ≠ 3 := exclude [0,3] (fun u v => edge r16 v u) (a 13) (a 5) 3 t5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t8 b9
  have b10 : a 14 ≠ 1 := exclude [0,1] (fun u v => edge r18 v u) (a 14) (a 6) 1 t7 c18 (by decide +kernel)
  have t10 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b10
  have b11 : a 14 ≠ 3 := exclude [0,1] (fun u v => edge r18 v u) (a 14) (a 6) 3 t7 c18 (by decide +kernel)
  have t11 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t10 b11
  have b12 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 12) (a 8) 1 d8 c22 (by decide +kernel)
  have t12 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b12
  have b13 : a 12 ≠ 3 := exclude [0,2] (fun u v => edge r22 v u) (a 12) (a 8) 3 d8 c22 (by decide +kernel)
  have t13 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t12 b13
  have b14 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r27 v u) (a 15) (a 11) 1 d11 c27 (by decide +kernel)
  have t14 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b14
  have b15 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 15) (a 11) 3 d11 c27 (by decide +kernel)
  have t15 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t14 b15
  exact And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t13 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d1 : a 1 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    : a 1 ∈ [0,1] ∧ a 2 ∈ [0,1] := by
  have b0 : a 1 ≠ 2 := exclude [0,1] (edge r4) (a 1) (a 3) 2 d3 c4 (by decide +kernel)
  have t0 : a 1 ∈ [0,1,3] := remove (a 1) 2 [0,1,2,3] d1 b0
  have b1 : a 1 ≠ 3 := exclude [0,1] (edge r4) (a 1) (a 3) 3 d3 c4 (by decide +kernel)
  have t1 : a 1 ∈ [0,1] := remove (a 1) 3 [0,1,3] t0 b1
  have b2 : a 2 ≠ 2 := exclude [0,1] (edge r8) (a 2) (a 6) 2 d6 c8 (by decide +kernel)
  have t2 : a 2 ∈ [0,1,3] := remove (a 2) 2 [0,1,2,3] d2 b2
  have b3 : a 2 ≠ 3 := exclude [0,1] (edge r8) (a 2) (a 6) 3 d6 c8 (by decide +kernel)
  have t3 : a 2 ∈ [0,1] := remove (a 2) 3 [0,1,3] t2 b3
  exact And.intro t1 (t3)

theorem chunk3 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,3])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d10 : a 10 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d7 : a 7 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d13 : a 13 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    (c31 : edge r31 (a 14) (a 15)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 7 ∈ [0] ∧ a 14 ∈ [0] ∧ a 8 ∈ [0] ∧ a 15 ∈ [0] ∧ a 11 ∈ [0] ∧ a 13 ∈ [0] ∧ a 9 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 3) (a 1) 1 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 3 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 3 [0,3] d5 b1
  have b2 : a 2 ≠ 1 := exclude [0] (edge r7) (a 2) (a 3) 1 t0 c7 (by decide +kernel)
  have t2 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b2
  have b3 : a 6 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 1 t2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b3
  have b4 : a 10 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 2 t2 c9 (by decide +kernel)
  have t4 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b4
  have b5 : a 4 ≠ 1 := exclude [0] (edge r12) (a 4) (a 5) 1 t1 c12 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b5
  have b6 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t5 c14 (by decide +kernel)
  have t6 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b6
  have b7 : a 7 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 7) (a 6) 1 t3 c17 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b7
  have b8 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 t3 c18 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b8
  have b9 : a 8 ≠ 2 := exclude [0] (edge r21) (a 8) (a 10) 2 t4 c21 (by decide +kernel)
  have t9 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b9
  have b10 : a 15 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 15) (a 14) 2 t8 c31 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b10
  have b11 : a 11 ≠ 2 := exclude [0] (edge r27) (a 11) (a 15) 2 t10 c27 (by decide +kernel)
  have t11 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b11
  have b12 : a 13 ≠ 2 := exclude [0] (edge r30) (a 13) (a 15) 2 t10 c30 (by decide +kernel)
  have t12 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b12
  have b13 : a 9 ≠ 2 := exclude [0] (edge r23) (a 9) (a 11) 2 t11 c23 (by decide +kernel)
  have t13 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

theorem chunk4 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,3])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d10 : a 10 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d7 : a 7 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d13 : a 13 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    (c31 : edge r31 (a 14) (a 15)=true)
    : a 3 ∈ [1] ∧ a 5 ∈ [3] ∧ a 2 ∈ [1] ∧ a 6 ∈ [1] ∧ a 10 ∈ [2] ∧ a 4 ∈ [1] ∧ a 12 ∈ [2] ∧ a 7 ∈ [1] ∧ a 14 ∈ [2] ∧ a 8 ∈ [2] ∧ a 15 ∈ [2] ∧ a 11 ∈ [2] ∧ a 13 ∈ [2] ∧ a 9 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r4 v u) (a 3) (a 1) 0 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 5) (a 1) 0 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [3] := remove (a 5) 0 [0,3] d5 b1
  have b2 : a 2 ≠ 0 := exclude [1] (edge r7) (a 2) (a 3) 0 t0 c7 (by decide +kernel)
  have t2 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b2
  have b3 : a 6 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 6) (a 2) 0 t2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b3
  have b4 : a 10 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 10) (a 2) 0 t2 c9 (by decide +kernel)
  have t4 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b4
  have b5 : a 4 ≠ 0 := exclude [3] (edge r12) (a 4) (a 5) 0 t1 c12 (by decide +kernel)
  have t5 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b5
  have b6 : a 12 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 12) (a 4) 0 t5 c14 (by decide +kernel)
  have t6 : a 12 ∈ [2] := remove (a 12) 0 [0,2] d12 b6
  have b7 : a 7 ≠ 0 := exclude [1] (fun u v => edge r17 v u) (a 7) (a 6) 0 t3 c17 (by decide +kernel)
  have t7 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b7
  have b8 : a 14 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 14) (a 6) 0 t3 c18 (by decide +kernel)
  have t8 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b8
  have b9 : a 8 ≠ 0 := exclude [2] (edge r21) (a 8) (a 10) 0 t4 c21 (by decide +kernel)
  have t9 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b9
  have b10 : a 15 ≠ 0 := exclude [2] (fun u v => edge r31 v u) (a 15) (a 14) 0 t8 c31 (by decide +kernel)
  have t10 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b10
  have b11 : a 11 ≠ 0 := exclude [2] (edge r27) (a 11) (a 15) 0 t10 c27 (by decide +kernel)
  have t11 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b11
  have b12 : a 13 ≠ 0 := exclude [2] (edge r30) (a 13) (a 15) 0 t10 c30 (by decide +kernel)
  have t12 : a 13 ∈ [2] := remove (a 13) 0 [0,2] d13 b12
  have b13 : a 9 ≠ 0 := exclude [2] (edge r23) (a 9) (a 11) 0 t11 c23 (by decide +kernel)
  have t13 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1,2,3])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1,2,3])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start6 : a 6 ∈ [0,1,2,3])
    (start7 : a 7 ∈ [0,1,2,3])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0) ∨
      (a 0=0 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 ∧ a 4=1 ∧ a 5=3 ∧ a 6=1 ∧ a 7=1 ∧ a 8=2 ∧ a 9=2 ∧ a 10=2 ∧ a 11=2 ∧ a 12=2 ∧ a 13=2 ∧ a 14=2 ∧ a 15=2) := by
  have group1 := chunk0 a start8 start0 start9 start1 start3 start2 start10 start7 start11 start5 start4 c3 c6 c7 c9 c10 c11 c12
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have group9 := chunk1 a h8 start4 start6 start13 start14 start12 h2 start15 h7 c12 c13 c16 c18 c22 c27
  rcases group9 with ⟨h10,h11,h12,h13,h14,h15⟩
  have group16 := chunk2 a start1 h4 start2 h11 c4 c8
  rcases group16 with ⟨h17,h18⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h17) with q19 | q20
  · have h21 : a 1 ∈ [0] := List.mem_singleton.mpr q19
    have group22 := chunk3 a h4 h21 h10 h18 h11 h5 start4 h14 h6 h13 h2 h15 h7 h12 h3 c4 c5 c7 c8 c9 c12 c14 c17 c18 c21 c23 c27 c30 c31
    rcases group22 with ⟨h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h21) (And.intro (forced (a 2) 0 h25) (And.intro (forced (a 3) 0 h23) (And.intro (forced (a 4) 0 h28) (And.intro (forced (a 5) 0 h24) (And.intro (forced (a 6) 0 h26) (And.intro (forced (a 7) 0 h30) (And.intro (forced (a 8) 0 h32) (And.intro (forced (a 9) 0 h36) (And.intro (forced (a 10) 0 h27) (And.intro (forced (a 11) 0 h34) (And.intro (forced (a 12) 0 h29) (And.intro (forced (a 13) 0 h35) (And.intro (forced (a 14) 0 h31) (forced (a 15) 0 h33))))))))))))))))
  · have h37 : a 1 ∈ [1] := List.mem_singleton.mpr q20
    have group38 := chunk4 a h4 h37 h10 h18 h11 h5 start4 h14 h6 h13 h2 h15 h7 h12 h3 c4 c5 c7 c8 c9 c12 c14 c17 c18 c21 c23 c27 c30 c31
    rcases group38 with ⟨h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h37) (And.intro (forced (a 2) 1 h41) (And.intro (forced (a 3) 1 h39) (And.intro (forced (a 4) 1 h44) (And.intro (forced (a 5) 3 h40) (And.intro (forced (a 6) 1 h42) (And.intro (forced (a 7) 1 h46) (And.intro (forced (a 8) 2 h48) (And.intro (forced (a 9) 2 h52) (And.intro (forced (a 10) 2 h43) (And.intro (forced (a 11) 2 h50) (And.intro (forced (a 12) 2 h45) (And.intro (forced (a 13) 2 h51) (And.intro (forced (a 14) 2 h47) (forced (a 15) 2 h49))))))))))))))))
#print axioms cover
end PartitionCover205_147
