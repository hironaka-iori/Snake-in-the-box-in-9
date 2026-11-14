import FiniteDomain205
namespace PartitionCover205_100
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[3]
def r5 : Array Nat := #[3]
def r6 : Array Nat := #[3]
def r7 : Array Nat := #[3]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[3]
def r10 : Array Nat := #[1,2]
def r11 : Array Nat := #[5,5]
def r12 : Array Nat := #[1,2]
def r13 : Array Nat := #[1,0]
def r14 : Array Nat := #[17,0]
def r15 : Array Nat := #[1,2]
def r16 : Array Nat := #[51,51]
def r17 : Array Nat := #[1]
def r18 : Array Nat := #[1]
def r19 : Array Nat := #[17,0]
def r20 : Array Nat := #[1,2]
def r21 : Array Nat := #[1,2]
def r22 : Array Nat := #[85,85]
def r23 : Array Nat := #[7,56]
def r24 : Array Nat := #[3,48]
def r25 : Array Nat := #[27,27]
def r26 : Array Nat := #[1,2]
def r27 : Array Nat := #[1,0,0,16,0,0]
def r28 : Array Nat := #[1,2,4,8,16,32,64,128]
def r29 : Array Nat := #[1,1,1,1,2,2,2,2]
def r30 : Array Nat := #[1,2,4,8,16,32,64,128]
def r31 : Array Nat := #[15,240]
theorem chunk0 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d3 : a 3 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (d5 : a 5 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (c11 : edge r11 (a 3) (a 11)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c17 : edge r17 (a 6) (a 7)=true)
    : a 11 ∈ [0,2] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0,4] ∧ a 13 ∈ [0,1,4,5] ∧ a 7 ∈ [0] := by
  have b0 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 1 d3 c11 (by decide +kernel)
  have t0 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b0
  have b1 : a 11 ≠ 3 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 3 d3 c11 (by decide +kernel)
  have t1 : a 11 ∈ [0,2,4,5] := remove (a 11) 3 [0,2,3,4,5] t0 b1
  have b2 : a 11 ≠ 4 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 4 d3 c11 (by decide +kernel)
  have t2 : a 11 ∈ [0,2,5] := remove (a 11) 4 [0,2,4,5] t1 b2
  have b3 : a 11 ≠ 5 := exclude [0,1] (fun u v => edge r11 v u) (a 11) (a 3) 5 d3 c11 (by decide +kernel)
  have t3 : a 11 ∈ [0,2] := remove (a 11) 5 [0,2,5] t2 b3
  have b4 : a 4 ≠ 1 := exclude [0] (edge r13) (a 4) (a 6) 1 d6 c13 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b4
  have b5 : a 12 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 1 t4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [0,2,3,4,5,6,7] := remove (a 12) 1 [0,1,2,3,4,5,6,7] d12 b5
  have b6 : a 12 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 2 t4 c14 (by decide +kernel)
  have t6 : a 12 ∈ [0,3,4,5,6,7] := remove (a 12) 2 [0,2,3,4,5,6,7] t5 b6
  have b7 : a 12 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 3 t4 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0,4,5,6,7] := remove (a 12) 3 [0,3,4,5,6,7] t6 b7
  have b8 : a 12 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 5 t4 c14 (by decide +kernel)
  have t8 : a 12 ∈ [0,4,6,7] := remove (a 12) 5 [0,4,5,6,7] t7 b8
  have b9 : a 12 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 6 t4 c14 (by decide +kernel)
  have t9 : a 12 ∈ [0,4,7] := remove (a 12) 6 [0,4,6,7] t8 b9
  have b10 : a 12 ≠ 7 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 7 t4 c14 (by decide +kernel)
  have t10 : a 12 ∈ [0,4] := remove (a 12) 7 [0,4,7] t9 b10
  have b11 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,1,3,4,5,6,7] := remove (a 13) 2 [0,1,2,3,4,5,6,7] d13 b11
  have b12 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,1,4,5,6,7] := remove (a 13) 3 [0,1,3,4,5,6,7] t11 b12
  have b13 : a 13 ≠ 6 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,1,4,5,7] := remove (a 13) 6 [0,1,4,5,6,7] t12 b13
  have b14 : a 13 ≠ 7 := exclude [0,1] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t14 : a 13 ∈ [0,1,4,5] := remove (a 13) 7 [0,1,4,5,7] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 7) (a 6) 1 d6 c17 (by decide +kernel)
  have t15 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b15
  exact And.intro t3 (And.intro t4 (And.intro t10 (And.intro t14 (t15))))

theorem chunk1 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7])
    (d7 : a 7 ∈ [0])
    (d9 : a 9 ∈ [0,1])
    (d11 : a 11 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,4,5])
    (d10 : a 10 ∈ [0,1])
    (d12 : a 12 ∈ [0,4])
    (d3 : a 3 ∈ [0,1])
    (c10 : edge r10 (a 3) (a 7)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c23 : edge r23 (a 9) (a 11)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    (c27 : edge r27 (a 11) (a 15)=true)
    (c28 : edge r28 (a 12) (a 13)=true)
    : a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 11 ∈ [0] ∧ a 10 ∈ [0] ∧ a 12 ∈ [0] ∧ a 3 ∈ [0] := by
  have b0 : a 14 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 1 d6 c18 (by decide +kernel)
  have t0 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b0
  have b1 : a 15 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 1 d7 c19 (by decide +kernel)
  have t1 : a 15 ∈ [0,2,3,4,5,6,7] := remove (a 15) 1 [0,1,2,3,4,5,6,7] d15 b1
  have b2 : a 15 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t2 : a 15 ∈ [0,3,4,5,6,7] := remove (a 15) 2 [0,2,3,4,5,6,7] t1 b2
  have b3 : a 15 ≠ 3 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t3 : a 15 ∈ [0,4,5,6,7] := remove (a 15) 3 [0,3,4,5,6,7] t2 b3
  have b4 : a 15 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 5 d7 c19 (by decide +kernel)
  have t4 : a 15 ∈ [0,4,6,7] := remove (a 15) 5 [0,4,5,6,7] t3 b4
  have b5 : a 15 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 6 d7 c19 (by decide +kernel)
  have t5 : a 15 ∈ [0,4,7] := remove (a 15) 6 [0,4,6,7] t4 b5
  have b6 : a 15 ≠ 7 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 7 d7 c19 (by decide +kernel)
  have t6 : a 15 ∈ [0,4] := remove (a 15) 7 [0,4,7] t5 b6
  have b7 : a 9 ≠ 1 := exclude [0,2] (edge r23) (a 9) (a 11) 1 d11 c23 (by decide +kernel)
  have t7 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b7
  have b8 : a 13 ≠ 4 := exclude [0] (fun u v => edge r24 v u) (a 13) (a 9) 4 t7 c24 (by decide +kernel)
  have t8 : a 13 ∈ [0,1,5] := remove (a 13) 4 [0,1,4,5] d13 b8
  have b9 : a 13 ≠ 5 := exclude [0] (fun u v => edge r24 v u) (a 13) (a 9) 5 t7 c24 (by decide +kernel)
  have t9 : a 13 ∈ [0,1] := remove (a 13) 5 [0,1,5] t8 b9
  have b10 : a 11 ≠ 2 := exclude [0,1] (fun u v => edge r25 v u) (a 11) (a 10) 2 d10 c25 (by decide +kernel)
  have t10 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b10
  have b11 : a 10 ≠ 1 := exclude [0] (edge r26) (a 10) (a 14) 1 t0 c26 (by decide +kernel)
  have t11 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b11
  have b12 : a 15 ≠ 4 := exclude [0] (fun u v => edge r27 v u) (a 15) (a 11) 4 t10 c27 (by decide +kernel)
  have t12 : a 15 ∈ [0] := remove (a 15) 4 [0,4] t6 b12
  have b13 : a 12 ≠ 4 := exclude [0,1] (edge r28) (a 12) (a 13) 4 t9 c28 (by decide +kernel)
  have t13 : a 12 ∈ [0] := remove (a 12) 4 [0,4] d12 b13
  have b14 : a 13 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 13) (a 12) 1 t13 c28 (by decide +kernel)
  have t14 : a 13 ∈ [0] := remove (a 13) 1 [0,1] t9 b14
  have b15 : a 3 ≠ 1 := exclude [0] (edge r10) (a 3) (a 7) 1 d7 c10 (by decide +kernel)
  have t15 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b15
  exact And.intro t0 (And.intro t12 (And.intro t7 (And.intro t14 (And.intro t10 (And.intro t11 (And.intro t13 (t15)))))))

theorem chunk2 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (c12 : edge r12 (a 4) (a 5)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    : a 5 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 5 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 5) (a 4) 1 d4 c12 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b0
  have b1 : a 8 ≠ 1 := exclude [0] (edge r20) (a 8) (a 9) 1 d9 c20 (by decide +kernel)
  have t1 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b1
  exact And.intro t0 (t1)
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2,3,4,5,6,7])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (start14 : a 14 ∈ [0,1])
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
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0) := by
  have group1 := chunk0 a start11 start3 start4 start6 start12 start13 start5 start7 c11 c13 c14 c16 c17
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  have group7 := chunk1 a start14 start6 start15 h6 start9 h2 h5 start10 h4 start3 c10 c18 c19 c23 c24 c25 c26 c27 c28
  rcases group7 with ⟨h8,h9,h10,h11,h12,h13,h14,h15⟩
  have group16 := chunk2 a start5 h3 start8 h10 c12 c20
  rcases group16 with ⟨h17,h18⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h15) (And.intro (forced (a 4) 0 h3) (And.intro (forced (a 5) 0 h17) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 h6) (And.intro (forced (a 8) 0 h18) (And.intro (forced (a 9) 0 h10) (And.intro (forced (a 10) 0 h13) (And.intro (forced (a 11) 0 h12) (And.intro (forced (a 12) 0 h14) (And.intro (forced (a 13) 0 h11) (And.intro (forced (a 14) 0 h8) (forced (a 15) 0 h9)))))))))))))))
#print axioms cover
end PartitionCover205_100
