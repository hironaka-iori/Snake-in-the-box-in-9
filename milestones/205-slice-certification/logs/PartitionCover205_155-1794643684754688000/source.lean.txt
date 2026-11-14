import FiniteDomain205
namespace PartitionCover205_155
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[3]
def r1 : Array Nat := #[3]
def r2 : Array Nat := #[51]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[1,2]
def r5 : Array Nat := #[1,2]
def r6 : Array Nat := #[1,4]
def r7 : Array Nat := #[1,2]
def r8 : Array Nat := #[15,240]
def r9 : Array Nat := #[1,2]
def r10 : Array Nat := #[1,2]
def r11 : Array Nat := #[3,12]
def r12 : Array Nat := #[1,0,0,0,2,0,0,0]
def r13 : Array Nat := #[1,2,4,8,16,32,64,128]
def r14 : Array Nat := #[1,0,0,0,4,0,0,0]
def r15 : Array Nat := #[1,2]
def r16 : Array Nat := #[1,4]
def r17 : Array Nat := #[1,0,0,0,2,0,0,0]
def r18 : Array Nat := #[1,0,0,0,4,0,0,0]
def r19 : Array Nat := #[3,12]
def r20 : Array Nat := #[5,5]
def r21 : Array Nat := #[1,2]
def r22 : Array Nat := #[3,12]
def r23 : Array Nat := #[1,2,4,8]
def r24 : Array Nat := #[1,0,4,0]
def r25 : Array Nat := #[1,4]
def r26 : Array Nat := #[1,4]
def r27 : Array Nat := #[3,0,12,0]
def r28 : Array Nat := #[1,0,4,0]
def r29 : Array Nat := #[1,2,4,8]
def r30 : Array Nat := #[1,2,4,8]
def r31 : Array Nat := #[1,0,4,0]
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (d0 : a 0 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (d12 : a 12 ∈ [0,1,2,3])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 4 ∈ [0,4] ∧ a 9 ∈ [0,2] ∧ a 6 ∈ [0,4] ∧ a 12 ∈ [0,2] := by
  have b0 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,1,3,4,5,6,7] := remove (a 4) 2 [0,1,2,3,4,5,6,7] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,1,4,5,6,7] := remove (a 4) 3 [0,1,3,4,5,6,7] t0 b1
  have b2 : a 4 ≠ 6 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 6 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,1,4,5,7] := remove (a 4) 6 [0,1,4,5,6,7] t1 b2
  have b3 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,1,4,5] := remove (a 4) 7 [0,1,4,5,7] t2 b3
  have b4 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r6 v u) (a 9) (a 1) 1 d1 c6 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b4
  have b5 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r6 v u) (a 9) (a 1) 3 d1 c6 (by decide +kernel)
  have t5 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t4 b5
  have b6 : a 4 ≠ 1 := exclude [0,1] (edge r12) (a 4) (a 5) 1 d5 c12 (by decide +kernel)
  have t6 : a 4 ∈ [0,4,5] := remove (a 4) 1 [0,1,4,5] t3 b6
  have b7 : a 4 ≠ 5 := exclude [0,1] (edge r12) (a 4) (a 5) 5 d5 c12 (by decide +kernel)
  have t7 : a 4 ∈ [0,4] := remove (a 4) 5 [0,4,5] t6 b7
  have b8 : a 6 ≠ 1 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 1 t7 c13 (by decide +kernel)
  have t8 : a 6 ∈ [0,2,3,4,5,6,7] := remove (a 6) 1 [0,1,2,3,4,5,6,7] d6 b8
  have b9 : a 6 ≠ 2 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 2 t7 c13 (by decide +kernel)
  have t9 : a 6 ∈ [0,3,4,5,6,7] := remove (a 6) 2 [0,2,3,4,5,6,7] t8 b9
  have b10 : a 6 ≠ 3 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 3 t7 c13 (by decide +kernel)
  have t10 : a 6 ∈ [0,4,5,6,7] := remove (a 6) 3 [0,3,4,5,6,7] t9 b10
  have b11 : a 6 ≠ 5 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 5 t7 c13 (by decide +kernel)
  have t11 : a 6 ∈ [0,4,6,7] := remove (a 6) 5 [0,4,5,6,7] t10 b11
  have b12 : a 6 ≠ 6 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 6 t7 c13 (by decide +kernel)
  have t12 : a 6 ∈ [0,4,7] := remove (a 6) 6 [0,4,6,7] t11 b12
  have b13 : a 6 ≠ 7 := exclude [0,4] (fun u v => edge r13 v u) (a 6) (a 4) 7 t7 c13 (by decide +kernel)
  have t13 : a 6 ∈ [0,4] := remove (a 6) 7 [0,4,7] t12 b13
  have b14 : a 12 ≠ 1 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 1 t7 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b14
  have b15 : a 12 ≠ 3 := exclude [0,4] (fun u v => edge r14 v u) (a 12) (a 4) 3 t7 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t14 b15
  exact And.intro t7 (And.intro t5 (And.intro t13 (t15)))

theorem chunk1 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,4])
    (d11 : a 11 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,2])
    (d15 : a 15 ∈ [0,1,2,3])
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    : a 13 ∈ [0,2] ∧ a 14 ∈ [0,2] ∧ a 11 ∈ [0,2] ∧ a 15 ∈ [0,2] := by
  have b0 : a 13 ≠ 1 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 1 d5 c16 (by decide +kernel)
  have t0 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b0
  have b1 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t1 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t0 b1
  have b2 : a 14 ≠ 1 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 1 d6 c18 (by decide +kernel)
  have t2 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b2
  have b3 : a 14 ≠ 3 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 3 d6 c18 (by decide +kernel)
  have t3 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t2 b3
  have b4 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r23 v u) (a 11) (a 9) 1 d9 c23 (by decide +kernel)
  have t4 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b4
  have b5 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r23 v u) (a 11) (a 9) 3 d9 c23 (by decide +kernel)
  have t5 : a 11 ∈ [0,2] := remove (a 11) 3 [0,2,3] t4 b5
  have b6 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r30 v u) (a 15) (a 13) 1 t1 c30 (by decide +kernel)
  have t6 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b6
  have b7 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r30 v u) (a 15) (a 13) 3 t1 c30 (by decide +kernel)
  have t7 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t6 b7
  exact And.intro t1 (And.intro t3 (And.intro t5 (t7)))

theorem chunk2 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,4])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,2])
    (d4 : a 4 ∈ [0,4])
    (d12 : a 12 ∈ [0,2])
    (d13 : a 13 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 3) (a 1) 1 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 1 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 9 ≠ 2 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 2 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b2
  have b3 : a 2 ≠ 1 := exclude [0] (edge r7) (a 2) (a 3) 1 t0 c7 (by decide +kernel)
  have t3 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b3
  have b4 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 t3 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b4
  have b5 : a 10 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 1 t3 c9 (by decide +kernel)
  have t5 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b5
  have b6 : a 7 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 1 t0 c10 (by decide +kernel)
  have t6 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b6
  have b7 : a 11 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 2 t0 c11 (by decide +kernel)
  have t7 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b7
  have b8 : a 4 ≠ 4 := exclude [0] (edge r12) (a 4) (a 5) 4 t1 c12 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 4 [0,4] d4 b8
  have b9 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t8 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b9
  have b10 : a 13 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 2 t1 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b10
  have b11 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 t4 c18 (by decide +kernel)
  have t11 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b11
  have b12 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 t6 c19 (by decide +kernel)
  have t12 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b12
  have b13 : a 8 ≠ 1 := exclude [0] (edge r21) (a 8) (a 10) 1 t5 c21 (by decide +kernel)
  have t13 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

theorem chunk3 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,4])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,2])
    (d4 : a 4 ∈ [0,4])
    (d12 : a 12 ∈ [0,2])
    (d13 : a 13 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    : a 3 ∈ [1] ∧ a 5 ∈ [1] ∧ a 9 ∈ [2] ∧ a 2 ∈ [1] ∧ a 6 ∈ [4] ∧ a 10 ∈ [1] ∧ a 7 ∈ [1] ∧ a 11 ∈ [2] ∧ a 4 ∈ [4] ∧ a 12 ∈ [2] ∧ a 13 ∈ [2] ∧ a 14 ∈ [2] ∧ a 15 ∈ [2] ∧ a 8 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r4 v u) (a 3) (a 1) 0 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 5) (a 1) 0 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 9 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 9) (a 1) 0 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b2
  have b3 : a 2 ≠ 0 := exclude [1] (edge r7) (a 2) (a 3) 0 t0 c7 (by decide +kernel)
  have t3 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b3
  have b4 : a 6 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 6) (a 2) 0 t3 c8 (by decide +kernel)
  have t4 : a 6 ∈ [4] := remove (a 6) 0 [0,4] d6 b4
  have b5 : a 10 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 10) (a 2) 0 t3 c9 (by decide +kernel)
  have t5 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b5
  have b6 : a 7 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 7) (a 3) 0 t0 c10 (by decide +kernel)
  have t6 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b6
  have b7 : a 11 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 11) (a 3) 0 t0 c11 (by decide +kernel)
  have t7 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b7
  have b8 : a 4 ≠ 0 := exclude [1] (edge r12) (a 4) (a 5) 0 t1 c12 (by decide +kernel)
  have t8 : a 4 ∈ [4] := remove (a 4) 0 [0,4] d4 b8
  have b9 : a 12 ≠ 0 := exclude [4] (fun u v => edge r14 v u) (a 12) (a 4) 0 t8 c14 (by decide +kernel)
  have t9 : a 12 ∈ [2] := remove (a 12) 0 [0,2] d12 b9
  have b10 : a 13 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 13) (a 5) 0 t1 c16 (by decide +kernel)
  have t10 : a 13 ∈ [2] := remove (a 13) 0 [0,2] d13 b10
  have b11 : a 14 ≠ 0 := exclude [4] (fun u v => edge r18 v u) (a 14) (a 6) 0 t4 c18 (by decide +kernel)
  have t11 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b11
  have b12 : a 15 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 15) (a 7) 0 t6 c19 (by decide +kernel)
  have t12 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b12
  have b13 : a 8 ≠ 0 := exclude [1] (edge r21) (a 8) (a 10) 0 t5 c21 (by decide +kernel)
  have t13 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=1 ∧ a 3=1 ∧ a 4=4 ∧ a 5=1 ∧ a 6=4 ∧ a 7=1 ∧ a 8=1 ∧ a 9=2 ∧ a 10=1 ∧ a 11=2 ∧ a 12=2 ∧ a 13=2 ∧ a 14=2 ∧ a 15=2) := by
  have group1 := chunk0 a start4 start0 start9 start1 start5 start6 start12 c2 c6 c12 c13 c14
  rcases group1 with ⟨h2,h3,h4,h5⟩
  have group6 := chunk1 a start13 start5 start14 h4 start11 h3 start15 c16 c18 c23 c30
  rcases group6 with ⟨h7,h8,h9,h10⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q11 | q12
  · have h13 : a 1 ∈ [0] := List.mem_singleton.mpr q11
    have group14 := chunk2 a start3 h13 start5 h3 start2 h4 start10 start7 h9 h2 h5 h7 h8 h10 start8 c4 c5 c6 c7 c8 c9 c10 c11 c12 c14 c16 c18 c19 c21
    rcases group14 with ⟨h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h13) (And.intro (forced (a 2) 0 h18) (And.intro (forced (a 3) 0 h15) (And.intro (forced (a 4) 0 h23) (And.intro (forced (a 5) 0 h16) (And.intro (forced (a 6) 0 h19) (And.intro (forced (a 7) 0 h21) (And.intro (forced (a 8) 0 h28) (And.intro (forced (a 9) 0 h17) (And.intro (forced (a 10) 0 h20) (And.intro (forced (a 11) 0 h22) (And.intro (forced (a 12) 0 h24) (And.intro (forced (a 13) 0 h25) (And.intro (forced (a 14) 0 h26) (forced (a 15) 0 h27))))))))))))))))
  · have h29 : a 1 ∈ [1] := List.mem_singleton.mpr q12
    have group30 := chunk3 a start3 h29 start5 h3 start2 h4 start10 start7 h9 h2 h5 h7 h8 h10 start8 c4 c5 c6 c7 c8 c9 c10 c11 c12 c14 c16 c18 c19 c21
    rcases group30 with ⟨h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h29) (And.intro (forced (a 2) 1 h34) (And.intro (forced (a 3) 1 h31) (And.intro (forced (a 4) 4 h39) (And.intro (forced (a 5) 1 h32) (And.intro (forced (a 6) 4 h35) (And.intro (forced (a 7) 1 h37) (And.intro (forced (a 8) 1 h44) (And.intro (forced (a 9) 2 h33) (And.intro (forced (a 10) 1 h36) (And.intro (forced (a 11) 2 h38) (And.intro (forced (a 12) 2 h40) (And.intro (forced (a 13) 2 h41) (And.intro (forced (a 14) 2 h42) (forced (a 15) 2 h43))))))))))))))))
#print axioms cover
end PartitionCover205_155
