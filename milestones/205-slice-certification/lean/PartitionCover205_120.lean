import FiniteDomain205
namespace PartitionCover205_120
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[3]
def r1 : Array Nat := #[15]
def r2 : Array Nat := #[15]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[3,12]
def r5 : Array Nat := #[1,2]
def r6 : Array Nat := #[1,2]
def r7 : Array Nat := #[1,2,4,8]
def r8 : Array Nat := #[3,12,48,192]
def r9 : Array Nat := #[1,1,2,2]
def r10 : Array Nat := #[17,0,68,0]
def r11 : Array Nat := #[1,0,2,0]
def r12 : Array Nat := #[1,2,4,8]
def r13 : Array Nat := #[3,48,0,0]
def r14 : Array Nat := #[3,12,48,192]
def r15 : Array Nat := #[3,12,48,192]
def r16 : Array Nat := #[3,12,48,192]
def r17 : Array Nat := #[1,0,0,0,4,0,0,0]
def r18 : Array Nat := #[3,3,0,0,12,12,0,0]
def r19 : Array Nat := #[5,2,5,8,80,32,80,128]
def r20 : Array Nat := #[1,2]
def r21 : Array Nat := #[1,2]
def r22 : Array Nat := #[15,15]
def r23 : Array Nat := #[1,2]
def r24 : Array Nat := #[1,4]
def r25 : Array Nat := #[3,3]
def r26 : Array Nat := #[15,15]
def r27 : Array Nat := #[5,5]
def r28 : Array Nat := #[5,0,5,0,80,0,80,0]
def r29 : Array Nat := #[1,2,4,8,16,32,64,128]
def r30 : Array Nat := #[1,2,4,8,16,32,64,128]
def r31 : Array Nat := #[1,1,4,4,16,16,64,64]
theorem chunk0 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7])
    (d4 : a 4 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (c5 : edge r5 (a 1) (a 5)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    : a 5 ∈ [0,1] ∧ a 3 ∈ [0,2] ∧ a 7 ∈ [0,2,4,6] ∧ a 4 ∈ [0,1] ∧ a 6 ∈ [0,1,4,5] ∧ a 12 ∈ [0,1,2,3,6,7] := by
  have b0 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 2 d1 c5 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,3] := remove (a 5) 2 [0,1,2,3] d5 b0
  have b1 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 3 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0,1] := remove (a 5) 3 [0,1,3] t0 b1
  have b2 : a 3 ≠ 1 := exclude [0,1,2,3,4,5,6,7] (edge r10) (a 3) (a 7) 1 d7 c10 (by decide +kernel)
  have t2 : a 3 ∈ [0,2,3] := remove (a 3) 1 [0,1,2,3] d3 b2
  have b3 : a 3 ≠ 3 := exclude [0,1,2,3,4,5,6,7] (edge r10) (a 3) (a 7) 3 d7 c10 (by decide +kernel)
  have t3 : a 3 ∈ [0,2] := remove (a 3) 3 [0,2,3] t2 b3
  have b4 : a 7 ≠ 1 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 1 t3 c10 (by decide +kernel)
  have t4 : a 7 ∈ [0,2,3,4,5,6,7] := remove (a 7) 1 [0,1,2,3,4,5,6,7] d7 b4
  have b5 : a 7 ≠ 3 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 3 t3 c10 (by decide +kernel)
  have t5 : a 7 ∈ [0,2,4,5,6,7] := remove (a 7) 3 [0,2,3,4,5,6,7] t4 b5
  have b6 : a 7 ≠ 5 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 5 t3 c10 (by decide +kernel)
  have t6 : a 7 ∈ [0,2,4,6,7] := remove (a 7) 5 [0,2,4,5,6,7] t5 b6
  have b7 : a 7 ≠ 7 := exclude [0,2] (fun u v => edge r10 v u) (a 7) (a 3) 7 t3 c10 (by decide +kernel)
  have t7 : a 7 ∈ [0,2,4,6] := remove (a 7) 7 [0,2,4,6,7] t6 b7
  have b8 : a 4 ≠ 2 := exclude [0,1] (edge r12) (a 4) (a 5) 2 t1 c12 (by decide +kernel)
  have t8 : a 4 ∈ [0,1,3] := remove (a 4) 2 [0,1,2,3] d4 b8
  have b9 : a 4 ≠ 3 := exclude [0,1] (edge r12) (a 4) (a 5) 3 t1 c12 (by decide +kernel)
  have t9 : a 4 ∈ [0,1] := remove (a 4) 3 [0,1,3] t8 b9
  have b10 : a 6 ≠ 2 := exclude [0,1] (fun u v => edge r13 v u) (a 6) (a 4) 2 t9 c13 (by decide +kernel)
  have t10 : a 6 ∈ [0,1,3,4,5,6,7] := remove (a 6) 2 [0,1,2,3,4,5,6,7] d6 b10
  have b11 : a 6 ≠ 3 := exclude [0,1] (fun u v => edge r13 v u) (a 6) (a 4) 3 t9 c13 (by decide +kernel)
  have t11 : a 6 ∈ [0,1,4,5,6,7] := remove (a 6) 3 [0,1,3,4,5,6,7] t10 b11
  have b12 : a 6 ≠ 6 := exclude [0,1] (fun u v => edge r13 v u) (a 6) (a 4) 6 t9 c13 (by decide +kernel)
  have t12 : a 6 ∈ [0,1,4,5,7] := remove (a 6) 6 [0,1,4,5,6,7] t11 b12
  have b13 : a 6 ≠ 7 := exclude [0,1] (fun u v => edge r13 v u) (a 6) (a 4) 7 t9 c13 (by decide +kernel)
  have t13 : a 6 ∈ [0,1,4,5] := remove (a 6) 7 [0,1,4,5,7] t12 b13
  have b14 : a 12 ≠ 4 := exclude [0,1] (fun u v => edge r14 v u) (a 12) (a 4) 4 t9 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,2,3,5,6,7] := remove (a 12) 4 [0,1,2,3,4,5,6,7] d12 b14
  have b15 : a 12 ≠ 5 := exclude [0,1] (fun u v => edge r14 v u) (a 12) (a 4) 5 t9 c14 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,2,3,6,7] := remove (a 12) 5 [0,1,2,3,5,6,7] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk1 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,2,3,6,7])
    (d4 : a 4 ∈ [0,1])
    (d7 : a 7 ∈ [0,2,4,6])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (d6 : a 6 ∈ [0,1,4,5])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7])
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 12 ∈ [0,1,2,3] ∧ a 7 ∈ [0,2] ∧ a 13 ∈ [0,1,2,3] ∧ a 6 ∈ [0,4] ∧ a 14 ∈ [0,1,2,3] ∧ a 15 ∈ [0,2,4,5,6,7] := by
  have b0 : a 12 ≠ 6 := exclude [0,1] (fun u v => edge r14 v u) (a 12) (a 4) 6 d4 c14 (by decide +kernel)
  have t0 : a 12 ∈ [0,1,2,3,7] := remove (a 12) 6 [0,1,2,3,6,7] d12 b0
  have b1 : a 12 ≠ 7 := exclude [0,1] (fun u v => edge r14 v u) (a 12) (a 4) 7 d4 c14 (by decide +kernel)
  have t1 : a 12 ∈ [0,1,2,3] := remove (a 12) 7 [0,1,2,3,7] t0 b1
  have b2 : a 7 ≠ 4 := exclude [0,1] (fun u v => edge r15 v u) (a 7) (a 5) 4 d5 c15 (by decide +kernel)
  have t2 : a 7 ∈ [0,2,6] := remove (a 7) 4 [0,2,4,6] d7 b2
  have b3 : a 7 ≠ 6 := exclude [0,1] (fun u v => edge r15 v u) (a 7) (a 5) 6 d5 c15 (by decide +kernel)
  have t3 : a 7 ∈ [0,2] := remove (a 7) 6 [0,2,6] t2 b3
  have b4 : a 13 ≠ 4 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t4 : a 13 ∈ [0,1,2,3,5,6,7] := remove (a 13) 4 [0,1,2,3,4,5,6,7] d13 b4
  have b5 : a 13 ≠ 5 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t5 : a 13 ∈ [0,1,2,3,6,7] := remove (a 13) 5 [0,1,2,3,5,6,7] t4 b5
  have b6 : a 13 ≠ 6 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t6 : a 13 ∈ [0,1,2,3,7] := remove (a 13) 6 [0,1,2,3,6,7] t5 b6
  have b7 : a 13 ≠ 7 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0,1,2,3] := remove (a 13) 7 [0,1,2,3,7] t6 b7
  have b8 : a 6 ≠ 1 := exclude [0,2] (edge r17) (a 6) (a 7) 1 t3 c17 (by decide +kernel)
  have t8 : a 6 ∈ [0,4,5] := remove (a 6) 1 [0,1,4,5] d6 b8
  have b9 : a 6 ≠ 5 := exclude [0,2] (edge r17) (a 6) (a 7) 5 t3 c17 (by decide +kernel)
  have t9 : a 6 ∈ [0,4] := remove (a 6) 5 [0,4,5] t8 b9
  have b10 : a 14 ≠ 4 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 4 t9 c18 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,2,3,5,6,7] := remove (a 14) 4 [0,1,2,3,4,5,6,7] d14 b10
  have b11 : a 14 ≠ 5 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 5 t9 c18 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,2,3,6,7] := remove (a 14) 5 [0,1,2,3,5,6,7] t10 b11
  have b12 : a 14 ≠ 6 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 6 t9 c18 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,2,3,7] := remove (a 14) 6 [0,1,2,3,6,7] t11 b12
  have b13 : a 14 ≠ 7 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 7 t9 c18 (by decide +kernel)
  have t13 : a 14 ∈ [0,1,2,3] := remove (a 14) 7 [0,1,2,3,7] t12 b13
  have b14 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 1 t3 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,2,3,4,5,6,7] := remove (a 15) 1 [0,1,2,3,4,5,6,7] d15 b14
  have b15 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 3 t3 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,2,4,5,6,7] := remove (a 15) 3 [0,2,3,4,5,6,7] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t7 (And.intro t9 (And.intro t13 (t15)))))

theorem chunk2 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,2,4,5,6,7])
    (d7 : a 7 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,2])
    (c7 : edge r7 (a 2) (a 3)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    (c29 : edge r29 (a 12) (a 14)=true)
    : a 15 ∈ [0,2] ∧ a 13 ∈ [0,2] ∧ a 12 ∈ [0,2] ∧ a 14 ∈ [0,2] ∧ a 2 ∈ [0,2] := by
  have b0 : a 15 ≠ 4 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 4 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,2,5,6,7] := remove (a 15) 4 [0,2,4,5,6,7] d15 b0
  have b1 : a 15 ≠ 5 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,2,6,7] := remove (a 15) 5 [0,2,5,6,7] t0 b1
  have b2 : a 15 ≠ 6 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 6 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,2,7] := remove (a 15) 6 [0,2,6,7] t1 b2
  have b3 : a 15 ≠ 7 := exclude [0,2] (fun u v => edge r19 v u) (a 15) (a 7) 7 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,2] := remove (a 15) 7 [0,2,7] t2 b3
  have b4 : a 13 ≠ 1 := exclude [0,1] (fun u v => edge r24 v u) (a 13) (a 9) 1 d9 c24 (by decide +kernel)
  have t4 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b4
  have b5 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r24 v u) (a 13) (a 9) 3 d9 c24 (by decide +kernel)
  have t5 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0,2] (edge r28) (a 12) (a 13) 1 t5 c28 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b6
  have b7 : a 12 ≠ 3 := exclude [0,2] (edge r28) (a 12) (a 13) 3 t5 c28 (by decide +kernel)
  have t7 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t6 b7
  have b8 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r29 v u) (a 14) (a 12) 1 t7 c29 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b8
  have b9 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r29 v u) (a 14) (a 12) 3 t7 c29 (by decide +kernel)
  have t9 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t8 b9
  have b10 : a 2 ≠ 1 := exclude [0,2] (edge r7) (a 2) (a 3) 1 d3 c7 (by decide +kernel)
  have t10 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b10
  have b11 : a 2 ≠ 3 := exclude [0,2] (edge r7) (a 2) (a 3) 3 d3 c7 (by decide +kernel)
  have t11 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t10 b11
  exact And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (t11))))

theorem chunk3 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,4])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d13 : a 13 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
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
    (c20 : edge r20 (a 8) (a 9)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0] ∧ a 8 ∈ [0] ∧ a 15 ∈ [0] := by
  have b0 : a 3 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 3) (a 1) 2 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 1 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 9 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 1 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b2
  have b3 : a 2 ≠ 2 := exclude [0] (edge r7) (a 2) (a 3) 2 t0 c7 (by decide +kernel)
  have t3 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b3
  have b4 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 t3 c8 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b4
  have b5 : a 10 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 1 t3 c9 (by decide +kernel)
  have t5 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b5
  have b6 : a 7 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 2 t0 c10 (by decide +kernel)
  have t6 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b6
  have b7 : a 11 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 1 t0 c11 (by decide +kernel)
  have t7 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b7
  have b8 : a 4 ≠ 1 := exclude [0] (edge r12) (a 4) (a 5) 1 t1 c12 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b8
  have b9 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t8 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b9
  have b10 : a 13 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 2 t1 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b10
  have b11 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 t4 c18 (by decide +kernel)
  have t11 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b11
  have b12 : a 8 ≠ 1 := exclude [0] (edge r20) (a 8) (a 9) 1 t2 c20 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b12
  have b13 : a 15 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 15) (a 13) 2 t10 c30 (by decide +kernel)
  have t13 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))

theorem chunk4 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,4])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d13 : a 13 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
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
    (c20 : edge r20 (a 8) (a 9)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    : a 3 ∈ [2] ∧ a 5 ∈ [1] ∧ a 9 ∈ [1] ∧ a 2 ∈ [2] ∧ a 6 ∈ [4] ∧ a 10 ∈ [1] ∧ a 7 ∈ [2] ∧ a 11 ∈ [1] ∧ a 4 ∈ [1] ∧ a 12 ∈ [2] ∧ a 13 ∈ [2] ∧ a 14 ∈ [2] ∧ a 8 ∈ [1] ∧ a 15 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r4 v u) (a 3) (a 1) 0 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 5) (a 1) 0 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 9 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 9) (a 1) 0 d1 c6 (by decide +kernel)
  have t2 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b2
  have b3 : a 2 ≠ 0 := exclude [2] (edge r7) (a 2) (a 3) 0 t0 c7 (by decide +kernel)
  have t3 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b3
  have b4 : a 6 ≠ 0 := exclude [2] (fun u v => edge r8 v u) (a 6) (a 2) 0 t3 c8 (by decide +kernel)
  have t4 : a 6 ∈ [4] := remove (a 6) 0 [0,4] d6 b4
  have b5 : a 10 ≠ 0 := exclude [2] (fun u v => edge r9 v u) (a 10) (a 2) 0 t3 c9 (by decide +kernel)
  have t5 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b5
  have b6 : a 7 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 7) (a 3) 0 t0 c10 (by decide +kernel)
  have t6 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b6
  have b7 : a 11 ≠ 0 := exclude [2] (fun u v => edge r11 v u) (a 11) (a 3) 0 t0 c11 (by decide +kernel)
  have t7 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b7
  have b8 : a 4 ≠ 0 := exclude [1] (edge r12) (a 4) (a 5) 0 t1 c12 (by decide +kernel)
  have t8 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b8
  have b9 : a 12 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 12) (a 4) 0 t8 c14 (by decide +kernel)
  have t9 : a 12 ∈ [2] := remove (a 12) 0 [0,2] d12 b9
  have b10 : a 13 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 13) (a 5) 0 t1 c16 (by decide +kernel)
  have t10 : a 13 ∈ [2] := remove (a 13) 0 [0,2] d13 b10
  have b11 : a 14 ≠ 0 := exclude [4] (fun u v => edge r18 v u) (a 14) (a 6) 0 t4 c18 (by decide +kernel)
  have t11 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b11
  have b12 : a 8 ≠ 0 := exclude [1] (edge r20) (a 8) (a 9) 0 t2 c20 (by decide +kernel)
  have t12 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b12
  have b13 : a 15 ≠ 0 := exclude [2] (fun u v => edge r30 v u) (a 15) (a 13) 0 t10 c30 (by decide +kernel)
  have t13 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1,2,3])
    (start3 : a 3 ∈ [0,1,2,3])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0,1])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7])
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
      (a 0=0 ∧ a 1=1 ∧ a 2=2 ∧ a 3=2 ∧ a 4=1 ∧ a 5=1 ∧ a 6=4 ∧ a 7=2 ∧ a 8=1 ∧ a 9=1 ∧ a 10=1 ∧ a 11=1 ∧ a 12=2 ∧ a 13=2 ∧ a 14=2 ∧ a 15=2) := by
  have group1 := chunk0 a start5 start1 start3 start7 start4 start6 start12 c5 c10 c12 c13 c14
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7⟩
  have group8 := chunk1 a h7 h5 h4 h2 start13 h6 start14 start15 c14 c15 c16 c17 c18 c19
  rcases group8 with ⟨h9,h10,h11,h12,h13,h14⟩
  have group15 := chunk2 a h14 h10 h11 start9 h9 h13 start2 h3 c7 c19 c24 c28 c29
  rcases group15 with ⟨h16,h17,h18,h19,h20⟩
  rcases (show a 1=0 ∨ a 1=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start1) with q21 | q22
  · have h23 : a 1 ∈ [0] := List.mem_singleton.mpr q21
    have group24 := chunk3 a h3 h23 h2 start9 h20 h12 start10 h10 start11 h5 h18 h17 h19 start8 h16 c4 c5 c6 c7 c8 c9 c10 c11 c12 c14 c16 c18 c20 c30
    rcases group24 with ⟨h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h23) (And.intro (forced (a 2) 0 h28) (And.intro (forced (a 3) 0 h25) (And.intro (forced (a 4) 0 h33) (And.intro (forced (a 5) 0 h26) (And.intro (forced (a 6) 0 h29) (And.intro (forced (a 7) 0 h31) (And.intro (forced (a 8) 0 h37) (And.intro (forced (a 9) 0 h27) (And.intro (forced (a 10) 0 h30) (And.intro (forced (a 11) 0 h32) (And.intro (forced (a 12) 0 h34) (And.intro (forced (a 13) 0 h35) (And.intro (forced (a 14) 0 h36) (forced (a 15) 0 h38))))))))))))))))
  · have h39 : a 1 ∈ [1] := List.mem_singleton.mpr q22
    have group40 := chunk4 a h3 h39 h2 start9 h20 h12 start10 h10 start11 h5 h18 h17 h19 start8 h16 c4 c5 c6 c7 c8 c9 c10 c11 c12 c14 c16 c18 c20 c30
    rcases group40 with ⟨h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 1 h39) (And.intro (forced (a 2) 2 h44) (And.intro (forced (a 3) 2 h41) (And.intro (forced (a 4) 1 h49) (And.intro (forced (a 5) 1 h42) (And.intro (forced (a 6) 4 h45) (And.intro (forced (a 7) 2 h47) (And.intro (forced (a 8) 1 h53) (And.intro (forced (a 9) 1 h43) (And.intro (forced (a 10) 1 h46) (And.intro (forced (a 11) 1 h48) (And.intro (forced (a 12) 2 h50) (And.intro (forced (a 13) 2 h51) (And.intro (forced (a 14) 2 h52) (forced (a 15) 2 h54))))))))))))))))
#print axioms cover
end PartitionCover205_120
