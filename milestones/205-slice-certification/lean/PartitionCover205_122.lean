import FiniteDomain205
namespace PartitionCover205_122
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[3]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[1,0]
def r5 : Array Nat := #[1,2]
def r6 : Array Nat := #[1,2]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[3]
def r10 : Array Nat := #[1]
def r11 : Array Nat := #[1]
def r12 : Array Nat := #[1,2]
def r13 : Array Nat := #[1,2]
def r14 : Array Nat := #[3,3]
def r15 : Array Nat := #[3,3]
def r16 : Array Nat := #[1,1]
def r17 : Array Nat := #[1,2]
def r18 : Array Nat := #[3,0]
def r19 : Array Nat := #[3,12]
def r20 : Array Nat := #[1,0]
def r21 : Array Nat := #[1,0]
def r22 : Array Nat := #[3,12]
def r23 : Array Nat := #[3,3]
def r24 : Array Nat := #[1,1]
def r25 : Array Nat := #[3,0]
def r26 : Array Nat := #[1,1]
def r27 : Array Nat := #[1,4]
def r28 : Array Nat := #[1,2,4,8]
def r29 : Array Nat := #[1,2,4,8]
def r30 : Array Nat := #[1,2,0,0]
def r31 : Array Nat := #[3,3,0,0]
theorem chunk0 (a : Nat → Nat)
    (d1 : a 1 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1,2,3])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c6 : edge r6 (a 1) (a 9)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    : a 1 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0,1] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0,1] ∧ a 15 ∈ [0,1] := by
  have b0 : a 1 ≠ 1 := exclude [0] (edge r4) (a 1) (a 3) 1 d3 c4 (by decide +kernel)
  have t0 : a 1 ∈ [0] := remove (a 1) 1 [0,1] d1 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 1 t0 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 9 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 9) (a 1) 1 t0 c6 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b2
  have b3 : a 6 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 1 d2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b3
  have b4 : a 7 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 1 d3 c10 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b4
  have b5 : a 11 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 1 d3 c11 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b5
  have b6 : a 4 ≠ 1 := exclude [0] (edge r12) (a 4) (a 5) 1 t1 c12 (by decide +kernel)
  have t6 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b6
  have b7 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t6 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0,1,3] := remove (a 12) 2 [0,1,2,3] d12 b7
  have b8 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t6 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0,1] := remove (a 12) 3 [0,1,3] t7 b8
  have b9 : a 13 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 1 t1 c16 (by decide +kernel)
  have t9 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b9
  have b10 : a 13 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 2 t1 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,3] := remove (a 13) 2 [0,2,3] t9 b10
  have b11 : a 13 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 3 t1 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0] := remove (a 13) 3 [0,3] t10 b11
  have b12 : a 14 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 2 t3 c18 (by decide +kernel)
  have t12 : a 14 ∈ [0,1,3] := remove (a 14) 2 [0,1,2,3] d14 b12
  have b13 : a 14 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 3 t3 c18 (by decide +kernel)
  have t13 : a 14 ∈ [0,1] := remove (a 14) 3 [0,1,3] t12 b13
  have b14 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 t4 c19 (by decide +kernel)
  have t14 : a 15 ∈ [0,1,3] := remove (a 15) 2 [0,1,2,3] d15 b14
  have b15 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 t4 c19 (by decide +kernel)
  have t15 : a 15 ∈ [0,1] := remove (a 15) 3 [0,1,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t11 (And.intro t13 (t15))))))))))

theorem chunk1 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    : a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 12 ∈ [0] := by
  have b0 : a 8 ≠ 1 := exclude [0] (edge r20) (a 8) (a 9) 1 d9 c20 (by decide +kernel)
  have t0 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b0
  have b1 : a 10 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 8) 1 t0 c21 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b1
  have b2 : a 14 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 10) 1 t1 c26 (by decide +kernel)
  have t2 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b2
  have b3 : a 15 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 1 d11 c27 (by decide +kernel)
  have t3 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b3
  have b4 : a 12 ≠ 1 := exclude [0] (edge r28) (a 12) (a 13) 1 d13 c28 (by decide +kernel)
  have t4 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0,1])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0,1])
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
  have group1 := chunk0 a start1 start3 start5 start9 start6 start2 start7 start11 start4 start12 start13 start14 start15 c4 c5 c6 c8 c10 c11 c12 c14 c16 c18 c19
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  have group13 := chunk1 a start8 h4 start10 h11 h12 h7 h9 h10 c20 c21 c26 c27 c28
  rcases group13 with ⟨h14,h15,h16,h17,h18⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 h2) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h8) (And.intro (forced (a 5) 0 h3) (And.intro (forced (a 6) 0 h5) (And.intro (forced (a 7) 0 h6) (And.intro (forced (a 8) 0 h14) (And.intro (forced (a 9) 0 h4) (And.intro (forced (a 10) 0 h15) (And.intro (forced (a 11) 0 h7) (And.intro (forced (a 12) 0 h18) (And.intro (forced (a 13) 0 h10) (And.intro (forced (a 14) 0 h16) (forced (a 15) 0 h17)))))))))))))))
#print axioms cover
end PartitionCover205_122
