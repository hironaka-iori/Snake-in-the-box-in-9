import FiniteDomain205
namespace PartitionCover205_103
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[15]
def r4 : Array Nat := #[1]
def r5 : Array Nat := #[3]
def r6 : Array Nat := #[15]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[1]
def r10 : Array Nat := #[3]
def r11 : Array Nat := #[1]
def r12 : Array Nat := #[3]
def r13 : Array Nat := #[1]
def r14 : Array Nat := #[63]
def r15 : Array Nat := #[3,2]
def r16 : Array Nat := #[15,0]
def r17 : Array Nat := #[1]
def r18 : Array Nat := #[3]
def r19 : Array Nat := #[3,12]
def r20 : Array Nat := #[1,2,4,8]
def r21 : Array Nat := #[1,2,4,8]
def r22 : Array Nat := #[1,0,8,0]
def r23 : Array Nat := #[1,2,4,8]
def r24 : Array Nat := #[1,2,4,8]
def r25 : Array Nat := #[1,2,4,8]
def r26 : Array Nat := #[1,1,2,2]
def r27 : Array Nat := #[1,0,0,0]
def r28 : Array Nat := #[1,0,0,4,0,0]
def r29 : Array Nat := #[3,0,0,3,0,0]
def r30 : Array Nat := #[1,0,0,0]
def r31 : Array Nat := #[1,5]
theorem chunk0 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1,2,3,4,5])
    (c9 : edge r9 (a 2) (a 10)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c22 : edge r22 (a 8) (a 12)=true)
    : a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 5 ∈ [0] ∧ a 7 ∈ [0] ∧ a 15 ∈ [0,1] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0,4,5] := by
  have b0 : a 10 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b0
  have b1 : a 10 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 2 d2 c9 (by decide +kernel)
  have t1 : a 10 ∈ [0,3] := remove (a 10) 2 [0,2,3] t0 b1
  have b2 : a 10 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 3 d2 c9 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 3 [0,3] t1 b2
  have b3 : a 11 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 1 d3 c11 (by decide +kernel)
  have t3 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b3
  have b4 : a 11 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 2 d3 c11 (by decide +kernel)
  have t4 : a 11 ∈ [0,3] := remove (a 11) 2 [0,2,3] t3 b4
  have b5 : a 11 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 3 [0,3] t4 b5
  have b6 : a 5 ≠ 1 := exclude [0,1,2,3] (edge r16) (a 5) (a 13) 1 d13 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b6
  have b7 : a 7 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 7) (a 6) 1 d6 c17 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b7
  have b8 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 t7 c19 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,3] := remove (a 15) 2 [0,1,2,3] d15 b8
  have b9 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 t7 c19 (by decide +kernel)
  have t9 : a 15 ∈ [0,1] := remove (a 15) 3 [0,1,3] t8 b9
  have b10 : a 8 ≠ 1 := exclude [0] (edge r21) (a 8) (a 10) 1 t2 c21 (by decide +kernel)
  have t10 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b10
  have b11 : a 8 ≠ 2 := exclude [0] (edge r21) (a 8) (a 10) 2 t2 c21 (by decide +kernel)
  have t11 : a 8 ∈ [0,3] := remove (a 8) 2 [0,2,3] t10 b11
  have b12 : a 8 ≠ 3 := exclude [0] (edge r21) (a 8) (a 10) 3 t2 c21 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 3 [0,3] t11 b12
  have b13 : a 12 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 8) 1 t12 c22 (by decide +kernel)
  have t13 : a 12 ∈ [0,2,3,4,5] := remove (a 12) 1 [0,1,2,3,4,5] d12 b13
  have b14 : a 12 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 8) 2 t12 c22 (by decide +kernel)
  have t14 : a 12 ∈ [0,3,4,5] := remove (a 12) 2 [0,2,3,4,5] t13 b14
  have b15 : a 12 ≠ 3 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 8) 3 t12 c22 (by decide +kernel)
  have t15 : a 12 ∈ [0,4,5] := remove (a 12) 3 [0,3,4,5] t14 b15
  exact And.intro t2 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t12 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,4,5])
    (d8 : a 8 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (c22 : edge r22 (a 8) (a 12)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    : a 12 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] := by
  have b0 : a 12 ≠ 4 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 8) 4 d8 c22 (by decide +kernel)
  have t0 : a 12 ∈ [0,5] := remove (a 12) 4 [0,4,5] d12 b0
  have b1 : a 12 ≠ 5 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 8) 5 d8 c22 (by decide +kernel)
  have t1 : a 12 ∈ [0] := remove (a 12) 5 [0,5] t0 b1
  have b2 : a 9 ≠ 1 := exclude [0] (edge r23) (a 9) (a 11) 1 d11 c23 (by decide +kernel)
  have t2 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b2
  have b3 : a 9 ≠ 2 := exclude [0] (edge r23) (a 9) (a 11) 2 d11 c23 (by decide +kernel)
  have t3 : a 9 ∈ [0,3] := remove (a 9) 2 [0,2,3] t2 b3
  have b4 : a 9 ≠ 3 := exclude [0] (edge r23) (a 9) (a 11) 3 d11 c23 (by decide +kernel)
  have t4 : a 9 ∈ [0] := remove (a 9) 3 [0,3] t3 b4
  have b5 : a 13 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 13) (a 9) 1 t4 c24 (by decide +kernel)
  have t5 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b5
  have b6 : a 13 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 13) (a 9) 2 t4 c24 (by decide +kernel)
  have t6 : a 13 ∈ [0,3] := remove (a 13) 2 [0,2,3] t5 b6
  have b7 : a 13 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 13) (a 9) 3 t4 c24 (by decide +kernel)
  have t7 : a 13 ∈ [0] := remove (a 13) 3 [0,3] t6 b7
  have b8 : a 14 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 10) 1 d10 c26 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b8
  have b9 : a 15 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 1 d11 c27 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b9
  exact And.intro t1 (And.intro t4 (And.intro t7 (And.intro t8 (t9))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1,2,3,4,5])
    (start13 : a 13 ∈ [0,1,2,3])
    (start14 : a 14 ∈ [0,1])
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
  have group1 := chunk0 a start10 start2 start11 start3 start5 start13 start7 start6 start15 start8 start12 c9 c11 c16 c17 c19 c21 c22
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have group9 := chunk1 a h8 h7 start9 h3 start13 start14 h2 h6 c22 c23 c24 c26 c27
  rcases group9 with ⟨h10,h11,h12,h13,h14⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 start4) (And.intro (forced (a 5) 0 h4) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 h5) (And.intro (forced (a 8) 0 h7) (And.intro (forced (a 9) 0 h11) (And.intro (forced (a 10) 0 h2) (And.intro (forced (a 11) 0 h3) (And.intro (forced (a 12) 0 h10) (And.intro (forced (a 13) 0 h12) (And.intro (forced (a 14) 0 h13) (forced (a 15) 0 h14)))))))))))))))
#print axioms cover
end PartitionCover205_103
