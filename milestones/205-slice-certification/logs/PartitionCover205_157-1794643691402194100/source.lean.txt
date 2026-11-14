import FiniteDomain205
namespace PartitionCover205_157
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[3]
def r1 : Array Nat := #[3]
def r2 : Array Nat := #[65]
def r3 : Array Nat := #[5]
def r4 : Array Nat := #[1,2]
def r5 : Array Nat := #[3,192]
def r6 : Array Nat := #[15,240]
def r7 : Array Nat := #[1,2]
def r8 : Array Nat := #[1,0]
def r9 : Array Nat := #[3,12]
def r10 : Array Nat := #[63,4032]
def r11 : Array Nat := #[9,9]
def r12 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r13 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r14 : Array Nat := #[195,195,12,12,48,48,195,195,768,768,3072,3072]
def r15 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r16 : Array Nat := #[3,3,12,12,48,48,192,192,768,768,3072,3072]
def r17 : Array Nat := #[325,1170,325,40,1170,40,325,1170,325,2560,1170,2560]
def r18 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r19 : Array Nat := #[715,2275,14,28,49,52,715,2275,896,1792,3136,3328]
def r20 : Array Nat := #[15,15,0,0]
def r21 : Array Nat := #[1,2,4,8]
def r22 : Array Nat := #[195,0,195,0]
def r23 : Array Nat := #[5,0,10,0,5,0,10,0]
def r24 : Array Nat := #[3,3,3,3,192,192,192,192]
def r25 : Array Nat := #[1,2,4,8]
def r26 : Array Nat := #[3,0,0,0]
def r27 : Array Nat := #[195,0,195,195]
def r28 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r29 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r30 : Array Nat := #[1,2,4,8,16,32,64,128,256,512,1024,2048]
def r31 : Array Nat := #[1,2,260,8,1040,32,64,128,260,512,1040,2048]
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    : a 4 ∈ [0,6] ∧ a 8 ∈ [0,2] ∧ a 5 ∈ [0,1,6,7,8,9,10,11] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 4) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d4 b0
  have b1 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 4) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 4) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 4 ≠ 4 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 4 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,5,6,7,8,9,10,11] := remove (a 4) 4 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 4 ≠ 5 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 5 d0 c2 (by decide +kernel)
  have t4 : a 4 ∈ [0,6,7,8,9,10,11] := remove (a 4) 5 [0,5,6,7,8,9,10,11] t3 b4
  have b5 : a 4 ≠ 7 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 7 d0 c2 (by decide +kernel)
  have t5 : a 4 ∈ [0,6,8,9,10,11] := remove (a 4) 7 [0,6,7,8,9,10,11] t4 b5
  have b6 : a 4 ≠ 8 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 8 d0 c2 (by decide +kernel)
  have t6 : a 4 ∈ [0,6,9,10,11] := remove (a 4) 8 [0,6,8,9,10,11] t5 b6
  have b7 : a 4 ≠ 9 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 9 d0 c2 (by decide +kernel)
  have t7 : a 4 ∈ [0,6,10,11] := remove (a 4) 9 [0,6,9,10,11] t6 b7
  have b8 : a 4 ≠ 10 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 10 d0 c2 (by decide +kernel)
  have t8 : a 4 ∈ [0,6,11] := remove (a 4) 10 [0,6,10,11] t7 b8
  have b9 : a 4 ≠ 11 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 11 d0 c2 (by decide +kernel)
  have t9 : a 4 ∈ [0,6] := remove (a 4) 11 [0,6,11] t8 b9
  have b10 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t10 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b10
  have b11 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t11 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t10 b11
  have b12 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 2 d1 c5 (by decide +kernel)
  have t12 : a 5 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 5) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d5 b12
  have b13 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 3 d1 c5 (by decide +kernel)
  have t13 : a 5 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 5) 3 [0,1,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 5 ≠ 4 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 4 d1 c5 (by decide +kernel)
  have t14 : a 5 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 5) 4 [0,1,4,5,6,7,8,9,10,11] t13 b14
  have b15 : a 5 ≠ 5 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 5 d1 c5 (by decide +kernel)
  have t15 : a 5 ∈ [0,1,6,7,8,9,10,11] := remove (a 5) 5 [0,1,5,6,7,8,9,10,11] t14 b15
  exact And.intro t9 (And.intro t11 (t15))

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,6,7,8,9,10,11])
    (d1 : a 1 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c5 : edge r5 (a 1) (a 5)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    : a 5 ∈ [0,1,6,7] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] := by
  have b0 : a 5 ≠ 8 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 8 d1 c5 (by decide +kernel)
  have t0 : a 5 ∈ [0,1,6,7,9,10,11] := remove (a 5) 8 [0,1,6,7,8,9,10,11] d5 b0
  have b1 : a 5 ≠ 9 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 9 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0,1,6,7,10,11] := remove (a 5) 9 [0,1,6,7,9,10,11] t0 b1
  have b2 : a 5 ≠ 10 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 10 d1 c5 (by decide +kernel)
  have t2 : a 5 ∈ [0,1,6,7,11] := remove (a 5) 10 [0,1,6,7,10,11] t1 b2
  have b3 : a 5 ≠ 11 := exclude [0,1] (fun u v => edge r5 v u) (a 5) (a 1) 11 d1 c5 (by decide +kernel)
  have t3 : a 5 ∈ [0,1,6,7] := remove (a 5) 11 [0,1,6,7,11] t2 b3
  have b4 : a 2 ≠ 1 := exclude [0,1,2,3,4,5,6,7,8,9,10,11] (edge r8) (a 2) (a 6) 1 d6 c8 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b4
  have b5 : a 6 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 1 t4 c8 (by decide +kernel)
  have t5 : a 6 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 6) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d6 b5
  have b6 : a 6 ≠ 2 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 2 t4 c8 (by decide +kernel)
  have t6 : a 6 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 6) 2 [0,2,3,4,5,6,7,8,9,10,11] t5 b6
  have b7 : a 6 ≠ 3 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 3 t4 c8 (by decide +kernel)
  have t7 : a 6 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 6) 3 [0,3,4,5,6,7,8,9,10,11] t6 b7
  have b8 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 t4 c8 (by decide +kernel)
  have t8 : a 6 ∈ [0,5,6,7,8,9,10,11] := remove (a 6) 4 [0,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 6 ≠ 5 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 5 t4 c8 (by decide +kernel)
  have t9 : a 6 ∈ [0,6,7,8,9,10,11] := remove (a 6) 5 [0,5,6,7,8,9,10,11] t8 b9
  have b10 : a 6 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 6 t4 c8 (by decide +kernel)
  have t10 : a 6 ∈ [0,7,8,9,10,11] := remove (a 6) 6 [0,6,7,8,9,10,11] t9 b10
  have b11 : a 6 ≠ 7 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 7 t4 c8 (by decide +kernel)
  have t11 : a 6 ∈ [0,8,9,10,11] := remove (a 6) 7 [0,7,8,9,10,11] t10 b11
  have b12 : a 6 ≠ 8 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 8 t4 c8 (by decide +kernel)
  have t12 : a 6 ∈ [0,9,10,11] := remove (a 6) 8 [0,8,9,10,11] t11 b12
  have b13 : a 6 ≠ 9 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 9 t4 c8 (by decide +kernel)
  have t13 : a 6 ∈ [0,10,11] := remove (a 6) 9 [0,9,10,11] t12 b13
  have b14 : a 6 ≠ 10 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 10 t4 c8 (by decide +kernel)
  have t14 : a 6 ∈ [0,11] := remove (a 6) 10 [0,10,11] t13 b14
  have b15 : a 6 ≠ 11 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 11 t4 c8 (by decide +kernel)
  have t15 : a 6 ∈ [0] := remove (a 6) 11 [0,11] t14 b15
  exact And.intro t3 (And.intro t4 (t15))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1])
    (d5 : a 5 ∈ [0,1,6,7])
    (d4 : a 4 ∈ [0,6])
    (d6 : a 6 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c9 : edge r9 (a 2) (a 10)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    : a 10 ∈ [0,1] ∧ a 11 ∈ [0,3] ∧ a 5 ∈ [0,6] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0,1,6,7] ∧ a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11] := by
  have b0 : a 10 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 2 d2 c9 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,3] := remove (a 10) 2 [0,1,2,3] d10 b0
  have b1 : a 10 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 3 d2 c9 (by decide +kernel)
  have t1 : a 10 ∈ [0,1] := remove (a 10) 3 [0,1,3] t0 b1
  have b2 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 1 d3 c11 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b2
  have b3 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 2 d3 c11 (by decide +kernel)
  have t3 : a 11 ∈ [0,3] := remove (a 11) 2 [0,2,3] t2 b3
  have b4 : a 5 ≠ 1 := exclude [0,6] (fun u v => edge r12 v u) (a 5) (a 4) 1 d4 c12 (by decide +kernel)
  have t4 : a 5 ∈ [0,6,7] := remove (a 5) 1 [0,1,6,7] d5 b4
  have b5 : a 5 ≠ 7 := exclude [0,6] (fun u v => edge r12 v u) (a 5) (a 4) 7 d4 c12 (by decide +kernel)
  have t5 : a 5 ∈ [0,6] := remove (a 5) 7 [0,6,7] t4 b5
  have b6 : a 4 ≠ 6 := exclude [0] (edge r13) (a 4) (a 6) 6 d6 c13 (by decide +kernel)
  have t6 : a 4 ∈ [0] := remove (a 4) 6 [0,6] d4 b6
  have b7 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t6 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 12) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d12 b7
  have b8 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t6 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 12) 3 [0,1,3,4,5,6,7,8,9,10,11] t7 b8
  have b9 : a 12 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 4 t6 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 12) 4 [0,1,4,5,6,7,8,9,10,11] t8 b9
  have b10 : a 12 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 5 t6 c14 (by decide +kernel)
  have t10 : a 12 ∈ [0,1,6,7,8,9,10,11] := remove (a 12) 5 [0,1,5,6,7,8,9,10,11] t9 b10
  have b11 : a 12 ≠ 8 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 8 t6 c14 (by decide +kernel)
  have t11 : a 12 ∈ [0,1,6,7,9,10,11] := remove (a 12) 8 [0,1,6,7,8,9,10,11] t10 b11
  have b12 : a 12 ≠ 9 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 9 t6 c14 (by decide +kernel)
  have t12 : a 12 ∈ [0,1,6,7,10,11] := remove (a 12) 9 [0,1,6,7,9,10,11] t11 b12
  have b13 : a 12 ≠ 10 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 10 t6 c14 (by decide +kernel)
  have t13 : a 12 ∈ [0,1,6,7,11] := remove (a 12) 10 [0,1,6,7,10,11] t12 b13
  have b14 : a 12 ≠ 11 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 11 t6 c14 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,6,7] := remove (a 12) 11 [0,1,6,7,11] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 1 t5 c15 (by decide +kernel)
  have t15 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d7 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t14 (t15)))))

theorem chunk3 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,6])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    : a 7 ∈ [0,6] ∧ a 13 ∈ [0,1,6,7,11] := by
  have b0 : a 7 ≠ 2 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 2 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 7) 2 [0,2,3,4,5,6,7,8,9,10,11] d7 b0
  have b1 : a 7 ≠ 3 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 3 d5 c15 (by decide +kernel)
  have t1 : a 7 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 7) 3 [0,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 7 ≠ 4 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 4 d5 c15 (by decide +kernel)
  have t2 : a 7 ∈ [0,5,6,7,8,9,10,11] := remove (a 7) 4 [0,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 7 ≠ 5 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 5 d5 c15 (by decide +kernel)
  have t3 : a 7 ∈ [0,6,7,8,9,10,11] := remove (a 7) 5 [0,5,6,7,8,9,10,11] t2 b3
  have b4 : a 7 ≠ 7 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 7 d5 c15 (by decide +kernel)
  have t4 : a 7 ∈ [0,6,8,9,10,11] := remove (a 7) 7 [0,6,7,8,9,10,11] t3 b4
  have b5 : a 7 ≠ 8 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 8 d5 c15 (by decide +kernel)
  have t5 : a 7 ∈ [0,6,9,10,11] := remove (a 7) 8 [0,6,8,9,10,11] t4 b5
  have b6 : a 7 ≠ 9 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 9 d5 c15 (by decide +kernel)
  have t6 : a 7 ∈ [0,6,10,11] := remove (a 7) 9 [0,6,9,10,11] t5 b6
  have b7 : a 7 ≠ 10 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 10 d5 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0,6,11] := remove (a 7) 10 [0,6,10,11] t6 b7
  have b8 : a 7 ≠ 11 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 11 d5 c15 (by decide +kernel)
  have t8 : a 7 ∈ [0,6] := remove (a 7) 11 [0,6,11] t7 b8
  have b9 : a 13 ≠ 2 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 13) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d13 b9
  have b10 : a 13 ≠ 3 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 13) 3 [0,1,3,4,5,6,7,8,9,10,11] t9 b10
  have b11 : a 13 ≠ 4 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 4 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 13) 4 [0,1,4,5,6,7,8,9,10,11] t10 b11
  have b12 : a 13 ≠ 5 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,6,7,8,9,10,11] := remove (a 13) 5 [0,1,5,6,7,8,9,10,11] t11 b12
  have b13 : a 13 ≠ 8 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 8 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,6,7,9,10,11] := remove (a 13) 8 [0,1,6,7,8,9,10,11] t12 b13
  have b14 : a 13 ≠ 9 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 9 d5 c16 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,6,7,10,11] := remove (a 13) 9 [0,1,6,7,9,10,11] t13 b14
  have b15 : a 13 ≠ 10 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 10 d5 c16 (by decide +kernel)
  have t15 : a 13 ∈ [0,1,6,7,11] := remove (a 13) 10 [0,1,6,7,10,11] t14 b15
  exact And.intro t8 (t15)

theorem chunk4 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,6,7,11])
    (d5 : a 5 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d7 : a 7 ∈ [0,6])
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 13 ∈ [0,1,6,7] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0,1,3,6,7,9,10,11] := by
  have b0 : a 13 ≠ 11 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 11 d5 c16 (by decide +kernel)
  have t0 : a 13 ∈ [0,1,6,7] := remove (a 13) 11 [0,1,6,7,11] d13 b0
  have b1 : a 14 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 1 d6 c18 (by decide +kernel)
  have t1 : a 14 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 14) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d14 b1
  have b2 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 d6 c18 (by decide +kernel)
  have t2 : a 14 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 14) 2 [0,2,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 d6 c18 (by decide +kernel)
  have t3 : a 14 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 14) 3 [0,3,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 14 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 4 d6 c18 (by decide +kernel)
  have t4 : a 14 ∈ [0,5,6,7,8,9,10,11] := remove (a 14) 4 [0,4,5,6,7,8,9,10,11] t3 b4
  have b5 : a 14 ≠ 5 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 5 d6 c18 (by decide +kernel)
  have t5 : a 14 ∈ [0,6,7,8,9,10,11] := remove (a 14) 5 [0,5,6,7,8,9,10,11] t4 b5
  have b6 : a 14 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 6 d6 c18 (by decide +kernel)
  have t6 : a 14 ∈ [0,7,8,9,10,11] := remove (a 14) 6 [0,6,7,8,9,10,11] t5 b6
  have b7 : a 14 ≠ 7 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 7 d6 c18 (by decide +kernel)
  have t7 : a 14 ∈ [0,8,9,10,11] := remove (a 14) 7 [0,7,8,9,10,11] t6 b7
  have b8 : a 14 ≠ 8 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 8 d6 c18 (by decide +kernel)
  have t8 : a 14 ∈ [0,9,10,11] := remove (a 14) 8 [0,8,9,10,11] t7 b8
  have b9 : a 14 ≠ 9 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 9 d6 c18 (by decide +kernel)
  have t9 : a 14 ∈ [0,10,11] := remove (a 14) 9 [0,9,10,11] t8 b9
  have b10 : a 14 ≠ 10 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 10 d6 c18 (by decide +kernel)
  have t10 : a 14 ∈ [0,11] := remove (a 14) 10 [0,10,11] t9 b10
  have b11 : a 14 ≠ 11 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 11 d6 c18 (by decide +kernel)
  have t11 : a 14 ∈ [0] := remove (a 14) 11 [0,11] t10 b11
  have b12 : a 15 ≠ 2 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,3,4,5,6,7,8,9,10,11] := remove (a 15) 2 [0,1,2,3,4,5,6,7,8,9,10,11] d15 b12
  have b13 : a 15 ≠ 4 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 4 d7 c19 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,3,5,6,7,8,9,10,11] := remove (a 15) 4 [0,1,3,4,5,6,7,8,9,10,11] t12 b13
  have b14 : a 15 ≠ 5 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,3,6,7,8,9,10,11] := remove (a 15) 5 [0,1,3,5,6,7,8,9,10,11] t13 b14
  have b15 : a 15 ≠ 8 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 8 d7 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,3,6,7,9,10,11] := remove (a 15) 8 [0,1,3,6,7,8,9,10,11] t14 b15
  exact And.intro t0 (And.intro t11 (t15))

theorem chunk5 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,3,6,7,9,10,11])
    (d7 : a 7 ∈ [0,6])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (d10 : a 10 ∈ [0,1])
    (d11 : a 11 ∈ [0,3])
    (d13 : a 13 ∈ [0,1,6,7])
    (d12 : a 12 ∈ [0,1,6,7])
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    : a 15 ∈ [0,1,6,7] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0,2] ∧ a 10 ∈ [0] ∧ a 13 ∈ [0,1] ∧ a 11 ∈ [0] ∧ a 12 ∈ [0,1,7] := by
  have b0 : a 15 ≠ 10 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 10 d7 c19 (by decide +kernel)
  have t0 : a 15 ∈ [0,1,3,6,7,9,11] := remove (a 15) 10 [0,1,3,6,7,9,10,11] d15 b0
  have b1 : a 15 ≠ 11 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 11 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,1,3,6,7,9] := remove (a 15) 11 [0,1,3,6,7,9,11] t0 b1
  have b2 : a 8 ≠ 2 := exclude [0,1,2,3,4,5,6,7] (edge r20) (a 8) (a 9) 2 d9 c20 (by decide +kernel)
  have t2 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b2
  have b3 : a 9 ≠ 4 := exclude [0] (fun u v => edge r20 v u) (a 9) (a 8) 4 t2 c20 (by decide +kernel)
  have t3 : a 9 ∈ [0,1,2,3,5,6,7] := remove (a 9) 4 [0,1,2,3,4,5,6,7] d9 b3
  have b4 : a 9 ≠ 5 := exclude [0] (fun u v => edge r20 v u) (a 9) (a 8) 5 t2 c20 (by decide +kernel)
  have t4 : a 9 ∈ [0,1,2,3,6,7] := remove (a 9) 5 [0,1,2,3,5,6,7] t3 b4
  have b5 : a 9 ≠ 6 := exclude [0] (fun u v => edge r20 v u) (a 9) (a 8) 6 t2 c20 (by decide +kernel)
  have t5 : a 9 ∈ [0,1,2,3,7] := remove (a 9) 6 [0,1,2,3,6,7] t4 b5
  have b6 : a 9 ≠ 7 := exclude [0] (fun u v => edge r20 v u) (a 9) (a 8) 7 t2 c20 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,2,3] := remove (a 9) 7 [0,1,2,3,7] t5 b6
  have b7 : a 10 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 1 t2 c21 (by decide +kernel)
  have t7 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b7
  have b8 : a 9 ≠ 1 := exclude [0,3] (edge r23) (a 9) (a 11) 1 d11 c23 (by decide +kernel)
  have t8 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] t6 b8
  have b9 : a 9 ≠ 3 := exclude [0,3] (edge r23) (a 9) (a 11) 3 d11 c23 (by decide +kernel)
  have t9 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t8 b9
  have b10 : a 13 ≠ 6 := exclude [0,2] (fun u v => edge r24 v u) (a 13) (a 9) 6 t9 c24 (by decide +kernel)
  have t10 : a 13 ∈ [0,1,7] := remove (a 13) 6 [0,1,6,7] d13 b10
  have b11 : a 13 ≠ 7 := exclude [0,2] (fun u v => edge r24 v u) (a 13) (a 9) 7 t9 c24 (by decide +kernel)
  have t11 : a 13 ∈ [0,1] := remove (a 13) 7 [0,1,7] t10 b11
  have b12 : a 11 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 11) (a 10) 3 t7 c25 (by decide +kernel)
  have t12 : a 11 ∈ [0] := remove (a 11) 3 [0,3] d11 b12
  have b13 : a 15 ≠ 3 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 3 t12 c27 (by decide +kernel)
  have t13 : a 15 ∈ [0,1,6,7,9] := remove (a 15) 3 [0,1,3,6,7,9] t1 b13
  have b14 : a 15 ≠ 9 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 9 t12 c27 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,6,7] := remove (a 15) 9 [0,1,6,7,9] t13 b14
  have b15 : a 12 ≠ 6 := exclude [0,1] (edge r28) (a 12) (a 13) 6 t11 c28 (by decide +kernel)
  have t15 : a 12 ∈ [0,1,7] := remove (a 12) 6 [0,1,6,7] d12 b15
  exact And.intro t14 (And.intro t2 (And.intro t9 (And.intro t7 (And.intro t11 (And.intro t12 (t15))))))

theorem chunk6 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1,7])
    (d13 : a 13 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d15 : a 15 ∈ [0,1,6,7])
    (d1 : a 1 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d7 : a 7 ∈ [0,6])
    (d5 : a 5 ∈ [0,6])
    (d4 : a 4 ∈ [0])
    (d11 : a 11 ∈ [0])
    (c6 : edge r6 (a 1) (a 9)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    (c29 : edge r29 (a 12) (a 14)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    (c31 : edge r31 (a 14) (a 15)=true)
    : a 12 ∈ [0] ∧ a 15 ∈ [0] ∧ a 1 ∈ [0] ∧ a 3 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 12 ≠ 7 := exclude [0,1] (edge r28) (a 12) (a 13) 7 d13 c28 (by decide +kernel)
  have t0 : a 12 ∈ [0,1] := remove (a 12) 7 [0,1,7] d12 b0
  have b1 : a 12 ≠ 1 := exclude [0] (edge r29) (a 12) (a 14) 1 d14 c29 (by decide +kernel)
  have t1 : a 12 ∈ [0] := remove (a 12) 1 [0,1] t0 b1
  have b2 : a 15 ≠ 6 := exclude [0,1] (fun u v => edge r30 v u) (a 15) (a 13) 6 d13 c30 (by decide +kernel)
  have t2 : a 15 ∈ [0,1,7] := remove (a 15) 6 [0,1,6,7] d15 b2
  have b3 : a 15 ≠ 7 := exclude [0,1] (fun u v => edge r30 v u) (a 15) (a 13) 7 d13 c30 (by decide +kernel)
  have t3 : a 15 ∈ [0,1] := remove (a 15) 7 [0,1,7] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 15) (a 14) 1 d14 c31 (by decide +kernel)
  have t4 : a 15 ∈ [0] := remove (a 15) 1 [0,1] t3 b4
  have b5 : a 1 ≠ 1 := exclude [0,2] (edge r6) (a 1) (a 9) 1 d9 c6 (by decide +kernel)
  have t5 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b5
  have b6 : a 3 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 1 d2 c7 (by decide +kernel)
  have t6 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b6
  have b7 : a 7 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 6 t6 c10 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 6 [0,6] d7 b7
  have b8 : a 5 ≠ 6 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 6 d4 c12 (by decide +kernel)
  have t8 : a 5 ∈ [0] := remove (a 5) 6 [0,6] d5 b8
  have b9 : a 9 ≠ 2 := exclude [0] (edge r23) (a 9) (a 11) 2 d11 c23 (by decide +kernel)
  have t9 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b9
  have b10 : a 13 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 13) (a 12) 1 t1 c28 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b10
  exact And.intro t1 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (t10)))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start5 : a 5 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start6 : a 6 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3,4,5,6,7])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start14 : a 14 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (start15 : a 15 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
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
  have group1 := chunk0 a start4 start0 start8 start5 start1 c2 c3 c5
  rcases group1 with ⟨h2,h3,h4⟩
  have group5 := chunk1 a h4 start1 start2 start6 c5 c8
  rcases group5 with ⟨h6,h7,h8⟩
  have group9 := chunk2 a start10 h7 start11 start3 h6 h2 h8 start12 start7 c9 c11 c12 c13 c14 c15
  rcases group9 with ⟨h10,h11,h12,h13,h14,h15⟩
  have group16 := chunk3 a h15 h12 start13 c15 c16
  rcases group16 with ⟨h17,h18⟩
  have group19 := chunk4 a h18 h12 start14 h8 start15 h17 c16 c18 c19
  rcases group19 with ⟨h20,h21,h22⟩
  have group23 := chunk5 a h22 h17 h3 start9 h10 h11 h20 h14 c19 c20 c21 c23 c24 c25 c27 c28
  rcases group23 with ⟨h24,h25,h26,h27,h28,h29,h30⟩
  have group31 := chunk6 a h30 h28 h21 h24 start1 h26 start3 h7 h17 h12 h13 h29 c6 c7 c10 c12 c23 c28 c29 c30 c31
  rcases group31 with ⟨h32,h33,h34,h35,h36,h37,h38,h39⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h34) (And.intro (forced (a 2) 0 h7) (And.intro (forced (a 3) 0 h35) (And.intro (forced (a 4) 0 h13) (And.intro (forced (a 5) 0 h37) (And.intro (forced (a 6) 0 h8) (And.intro (forced (a 7) 0 h36) (And.intro (forced (a 8) 0 h25) (And.intro (forced (a 9) 0 h38) (And.intro (forced (a 10) 0 h27) (And.intro (forced (a 11) 0 h29) (And.intro (forced (a 12) 0 h32) (And.intro (forced (a 13) 0 h39) (And.intro (forced (a 14) 0 h21) (forced (a 15) 0 h33)))))))))))))))
#print axioms cover
end PartitionCover205_157
