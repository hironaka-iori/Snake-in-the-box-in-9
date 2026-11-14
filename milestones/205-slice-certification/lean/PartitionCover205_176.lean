import FiniteDomain205
namespace PartitionCover205_176
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[3]
def r5 : Array Nat := #[7]
def r6 : Array Nat := #[1]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[1]
def r9 : Array Nat := #[5]
def r10 : Array Nat := #[3]
def r11 : Array Nat := #[63]
def r12 : Array Nat := #[1]
def r13 : Array Nat := #[3,0,0]
def r14 : Array Nat := #[5,5,5]
def r15 : Array Nat := #[1,1,1]
def r16 : Array Nat := #[1]
def r17 : Array Nat := #[1]
def r18 : Array Nat := #[1]
def r19 : Array Nat := #[9]
def r20 : Array Nat := #[3]
def r21 : Array Nat := #[7]
def r22 : Array Nat := #[9]
def r23 : Array Nat := #[3,3]
def r24 : Array Nat := #[3,12]
def r25 : Array Nat := #[3,2]
def r26 : Array Nat := #[5,0]
def r27 : Array Nat := #[1,2]
def r28 : Array Nat := #[1,1,0,0,2,2]
def r29 : Array Nat := #[1,2,4,8,16,32]
def r30 : Array Nat := #[1,2,4,2,4,1]
def r31 : Array Nat := #[3,3,0,0,3,3]
def r32 : Array Nat := #[5,24,34,24]
def r33 : Array Nat := #[5,3,5,3]
def r34 : Array Nat := #[1,1,2,2]
def r35 : Array Nat := #[5,0,24,0,24,5]
def r36 : Array Nat := #[1,2,4,8,0,0]
def r37 : Array Nat := #[1,1,1,1,1,1]
def r38 : Array Nat := #[3,0,0,0,6,0]
def r39 : Array Nat := #[1,1,2,2,4,4]
def r40 : Array Nat := #[1,2,4]
def r41 : Array Nat := #[1,10,4]
def r42 : Array Nat := #[5,8,2]
def r43 : Array Nat := #[1,2,4]
def r44 : Array Nat := #[15,10,5]
def r45 : Array Nat := #[1,2,4,2]
def r46 : Array Nat := #[3,12,48,192]
def r47 : Array Nat := #[3,3,3]
def r48 : Array Nat := #[1,1]
def r49 : Array Nat := #[1,2]
def r50 : Array Nat := #[7,56]
def r51 : Array Nat := #[3,3]
def r52 : Array Nat := #[1]
def r53 : Array Nat := #[9]
def r54 : Array Nat := #[3]
def r55 : Array Nat := #[1,1]
def r56 : Array Nat := #[7,7]
def r57 : Array Nat := #[1,2]
def r58 : Array Nat := #[3]
def r59 : Array Nat := #[7]
def r60 : Array Nat := #[1,2,4,8,16,32]
def r61 : Array Nat := #[1,1,1,4,4,4]
def r62 : Array Nat := #[5,4,1,80,64,16]
def r63 : Array Nat := #[1,0,0,2,0,0]
def r64 : Array Nat := #[3,0,0,12,0,0]
def r65 : Array Nat := #[1,3,2]
def r66 : Array Nat := #[225,68,170]
def r67 : Array Nat := #[3,12]
def r68 : Array Nat := #[1,2]
def r69 : Array Nat := #[1,2]
def r70 : Array Nat := #[85,85]
def r71 : Array Nat := #[1,1]
def r72 : Array Nat := #[3,12]
def r73 : Array Nat := #[1,1]
def r74 : Array Nat := #[81,2]
def r75 : Array Nat := #[5,0,0]
def r76 : Array Nat := #[1,1,2,2,4,4,8,8]
def r77 : Array Nat := #[17,17,68,65,26,170,68,170]
def r78 : Array Nat := #[1,2,4,8]
def r79 : Array Nat := #[3,12,0,12,0,12,0,12]
theorem chunk0 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1,2,3,4,5])
    (d0 : a 0 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0])
    (d3 : a 3 ∈ [0,1,2])
    (d2 : a 2 ∈ [0])
    (d18 : a 18 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3,4,5])
    (d6 : a 6 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d12 : a 12 ∈ [0,1,2])
    (c3 : edge r3 (a 0) (a 8)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    : a 8 ∈ [0,1] ∧ a 9 ∈ [0] ∧ a 3 ∈ [0] ∧ a 18 ∈ [0] ∧ a 11 ∈ [0,2] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0,2] := by
  have b0 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t0 : a 8 ∈ [0,1,3,4,5] := remove (a 8) 2 [0,1,2,3,4,5] d8 b0
  have b1 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t1 : a 8 ∈ [0,1,4,5] := remove (a 8) 3 [0,1,3,4,5] t0 b1
  have b2 : a 8 ≠ 4 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 4 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,5] := remove (a 8) 4 [0,1,4,5] t1 b2
  have b3 : a 8 ≠ 5 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 5 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1] := remove (a 8) 5 [0,1,5] t2 b3
  have b4 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b4
  have b5 : a 9 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 2 d1 c7 (by decide +kernel)
  have t5 : a 9 ∈ [0,3] := remove (a 9) 2 [0,2,3] t4 b5
  have b6 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t6 : a 9 ∈ [0] := remove (a 9) 3 [0,3] t5 b6
  have b7 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t7 : a 3 ∈ [0,2] := remove (a 3) 1 [0,1,2] d3 b7
  have b8 : a 18 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 1 d2 c12 (by decide +kernel)
  have t8 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b8
  have b9 : a 3 ≠ 2 := exclude [0,1] (edge r13) (a 3) (a 7) 2 d7 c13 (by decide +kernel)
  have t9 : a 3 ∈ [0] := remove (a 3) 2 [0,2] t7 b9
  have b10 : a 11 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 1 t9 c14 (by decide +kernel)
  have t10 : a 11 ∈ [0,2,3,4,5] := remove (a 11) 1 [0,1,2,3,4,5] d11 b10
  have b11 : a 11 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 3 t9 c14 (by decide +kernel)
  have t11 : a 11 ∈ [0,2,4,5] := remove (a 11) 3 [0,2,3,4,5] t10 b11
  have b12 : a 11 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 4 t9 c14 (by decide +kernel)
  have t12 : a 11 ∈ [0,2,5] := remove (a 11) 4 [0,2,4,5] t11 b12
  have b13 : a 11 ≠ 5 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 5 t9 c14 (by decide +kernel)
  have t13 : a 11 ∈ [0,2] := remove (a 11) 5 [0,2,5] t12 b13
  have b14 : a 6 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 1 d4 c17 (by decide +kernel)
  have t14 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b14
  have b15 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 d4 c18 (by decide +kernel)
  have t15 : a 12 ∈ [0,2] := remove (a 12) 1 [0,1,2] d12 b15
  exact And.intro t3 (And.intro t6 (And.intro t9 (And.intro t8 (And.intro t13 (And.intro t14 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,2])
    (d4 : a 4 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d5 : a 5 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d22 : a 22 ∈ [0,1,2])
    (d7 : a 7 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2])
    (d23 : a 23 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3,4,5])
    (d8 : a 8 ∈ [0,1])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    : a 12 ∈ [0] ∧ a 20 ∈ [0,3] ∧ a 21 ∈ [0,3] ∧ a 14 ∈ [0,1] ∧ a 22 ∈ [0,1] ∧ a 7 ∈ [0] ∧ a 15 ∈ [0,2] ∧ a 23 ∈ [0] ∧ a 10 ∈ [0,1,3,4,5] := by
  have b0 : a 12 ≠ 2 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 2 d4 c18 (by decide +kernel)
  have t0 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b0
  have b1 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 d4 c19 (by decide +kernel)
  have t1 : a 20 ∈ [0,2,3,4,5] := remove (a 20) 1 [0,1,2,3,4,5] d20 b1
  have b2 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [0,3,4,5] := remove (a 20) 2 [0,2,3,4,5] t1 b2
  have b3 : a 20 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 4 d4 c19 (by decide +kernel)
  have t3 : a 20 ∈ [0,3,5] := remove (a 20) 4 [0,3,4,5] t2 b3
  have b4 : a 20 ≠ 5 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 5 d4 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0,3] := remove (a 20) 5 [0,3,5] t3 b4
  have b5 : a 21 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 1 d5 c22 (by decide +kernel)
  have t5 : a 21 ∈ [0,2,3,4,5] := remove (a 21) 1 [0,1,2,3,4,5] d21 b5
  have b6 : a 21 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 2 d5 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0,3,4,5] := remove (a 21) 2 [0,2,3,4,5] t5 b6
  have b7 : a 21 ≠ 4 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 4 d5 c22 (by decide +kernel)
  have t7 : a 21 ∈ [0,3,5] := remove (a 21) 4 [0,3,4,5] t6 b7
  have b8 : a 21 ≠ 5 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 5 d5 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0,3] := remove (a 21) 5 [0,3,5] t7 b8
  have b9 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 d6 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,3] := remove (a 14) 2 [0,1,2,3] d14 b9
  have b10 : a 14 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 3 d6 c24 (by decide +kernel)
  have t10 : a 14 ∈ [0,1] := remove (a 14) 3 [0,1,3] t9 b10
  have b11 : a 22 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1] := remove (a 22) 2 [0,1,2] d22 b11
  have b12 : a 7 ≠ 1 := exclude [0,1,2] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t12 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b12
  have b13 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 t12 c26 (by decide +kernel)
  have t13 : a 15 ∈ [0,2] := remove (a 15) 1 [0,1,2] d15 b13
  have b14 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 t12 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b14
  have b15 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 2 d8 c29 (by decide +kernel)
  have t15 : a 10 ∈ [0,1,3,4,5] := remove (a 10) 2 [0,1,2,3,4,5] d10 b15
  exact And.intro t0 (And.intro t4 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,3,4,5])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d13 : a 13 ∈ [0,1,2])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d11 : a 11 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2])
    (d28 : a 28 ∈ [0,1,2,3,4,5,6,7])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 10 ∈ [0] ∧ a 8 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0] ∧ a 11 ∈ [0] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0,2,4,5,6,7] := by
  have b0 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 3 d8 c29 (by decide +kernel)
  have t0 : a 10 ∈ [0,1,4,5] := remove (a 10) 3 [0,1,3,4,5] d10 b0
  have b1 : a 10 ≠ 4 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 4 d8 c29 (by decide +kernel)
  have t1 : a 10 ∈ [0,1,5] := remove (a 10) 4 [0,1,4,5] t0 b1
  have b2 : a 10 ≠ 5 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 5 d8 c29 (by decide +kernel)
  have t2 : a 10 ∈ [0,1] := remove (a 10) 5 [0,1,5] t1 b2
  have b3 : a 8 ≠ 1 := exclude [0] (edge r30) (a 8) (a 12) 1 d12 c30 (by decide +kernel)
  have t3 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b3
  have b4 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0,2] := remove (a 13) 1 [0,1,2] d13 b4
  have b5 : a 25 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 1 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b5
  have b6 : a 10 ≠ 1 := exclude [0,2] (edge r35) (a 10) (a 11) 1 d11 c35 (by decide +kernel)
  have t6 : a 10 ∈ [0] := remove (a 10) 1 [0,1] t2 b6
  have b7 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 t6 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b7
  have b8 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t6 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b8
  have b9 : a 11 ≠ 2 := exclude [0,2] (edge r38) (a 11) (a 15) 2 d15 c38 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b9
  have b10 : a 15 ≠ 2 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 2 t9 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b10
  have b11 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 t9 c39 (by decide +kernel)
  have t11 : a 27 ∈ [0,2] := remove (a 27) 1 [0,1,2] d27 b11
  have b12 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 t9 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0] := remove (a 27) 2 [0,2] t11 b12
  have b13 : a 13 ≠ 2 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 2 d12 c40 (by decide +kernel)
  have t13 : a 13 ∈ [0] := remove (a 13) 2 [0,2] t4 b13
  have b14 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t14 : a 28 ∈ [0,2,3,4,5,6,7] := remove (a 28) 1 [0,1,2,3,4,5,6,7] d28 b14
  have b15 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0,2,4,5,6,7] := remove (a 28) 3 [0,2,3,4,5,6,7] t14 b15
  exact And.intro t6 (And.intro t3 (And.intro t13 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t12 (t15)))))))))

theorem chunk3 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,2,4,5,6,7])
    (d12 : a 12 ∈ [0])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d20 : a 20 ∈ [0,3])
    (d21 : a 21 ∈ [0,3])
    (d22 : a 22 ∈ [0,1])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    : a 28 ∈ [0,2] ∧ a 30 ∈ [0,1] ∧ a 31 ∈ [0,1] ∧ a 16 ∈ [0] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0,2,5,6,7] := remove (a 28) 4 [0,2,4,5,6,7] d28 b0
  have b1 : a 28 ≠ 5 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t1 : a 28 ∈ [0,2,6,7] := remove (a 28) 5 [0,2,5,6,7] t0 b1
  have b2 : a 28 ≠ 6 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 6 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [0,2,7] := remove (a 28) 6 [0,2,6,7] t1 b2
  have b3 : a 28 ≠ 7 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 7 d12 c42 (by decide +kernel)
  have t3 : a 28 ∈ [0,2] := remove (a 28) 7 [0,2,7] t2 b3
  have b4 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,1,3,4,5,6,7] := remove (a 30) 2 [0,1,2,3,4,5,6,7] d30 b4
  have b5 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t5 : a 30 ∈ [0,1,4,5,6,7] := remove (a 30) 3 [0,1,3,4,5,6,7] t4 b5
  have b6 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,5,6,7] := remove (a 30) 4 [0,1,4,5,6,7] t5 b6
  have b7 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t7 : a 30 ∈ [0,1,6,7] := remove (a 30) 5 [0,1,5,6,7] t6 b7
  have b8 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,7] := remove (a 30) 6 [0,1,6,7] t7 b8
  have b9 : a 30 ≠ 7 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 7 d14 c46 (by decide +kernel)
  have t9 : a 30 ∈ [0,1] := remove (a 30) 7 [0,1,7] t8 b9
  have b10 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b10
  have b11 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t10 b11
  have b12 : a 16 ≠ 1 := exclude [0] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t12 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b12
  have b13 : a 20 ≠ 3 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 3 t12 c50 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 3 [0,3] d20 b13
  have b14 : a 21 ≠ 3 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 3 t13 c60 (by decide +kernel)
  have t14 : a 21 ∈ [0] := remove (a 21) 3 [0,3] d21 b14
  have b15 : a 22 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 22) (a 20) 1 t13 c61 (by decide +kernel)
  have t15 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b15
  exact And.intro t3 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))

theorem chunk4 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d28 : a 28 ∈ [0,2])
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 24 ∈ [0] ∧ a 31 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 d21 c64 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,3] := remove (a 29) 2 [0,1,2,3] d29 b0
  have b1 : a 29 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 3 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0,1] := remove (a 29) 3 [0,1,3] t0 b1
  have b2 : a 30 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b2
  have b3 : a 24 ≠ 1 := exclude [0] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t3 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b3
  have b4 : a 31 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 1 d27 c75 (by decide +kernel)
  have t4 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b4
  have b5 : a 28 ≠ 2 := exclude [0] (edge r77) (a 28) (a 30) 2 t2 c77 (by decide +kernel)
  have t5 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b5
  have b6 : a 29 ≠ 1 := exclude [0] (edge r78) (a 29) (a 31) 1 t4 c78 (by decide +kernel)
  have t6 : a 29 ∈ [0] := remove (a 29) 1 [0,1] t1 b6
  exact And.intro t6 (And.intro t2 (And.intro t3 (And.intro t4 (t5))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1,2])
    (start4 : a 4 ∈ [0])
    (start5 : a 5 ∈ [0])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1,2,3,4,5])
    (start9 : a 9 ∈ [0,1,2,3])
    (start10 : a 10 ∈ [0,1,2,3,4,5])
    (start11 : a 11 ∈ [0,1,2,3,4,5])
    (start12 : a 12 ∈ [0,1,2])
    (start13 : a 13 ∈ [0,1,2])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1,2])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2])
    (start23 : a 23 ∈ [0,1])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0,1])
    (start26 : a 26 ∈ [0,1])
    (start27 : a 27 ∈ [0,1,2])
    (start28 : a 28 ∈ [0,1,2,3,4,5,6,7])
    (start29 : a 29 ∈ [0,1,2,3])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6,7])
    (start31 : a 31 ∈ [0,1,2,3])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c23 : edge r23 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0) := by
  have group1 := chunk0 a start8 start0 start9 start1 start3 start2 start18 start7 start11 start6 start4 start12 c3 c7 c9 c12 c13 c14 c17 c18
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have group9 := chunk1 a h8 start4 start20 start21 start5 start14 h7 start22 start7 start15 start23 start10 h2 c18 c19 c22 c24 c25 c26 c27 c29
  rcases group9 with ⟨h10,h11,h12,h13,h14,h15,h16,h17,h18⟩
  have group19 := chunk2 a h18 h2 h10 start13 h3 start25 h6 h13 start26 h16 start27 start28 c29 c30 c33 c34 c35 c36 c37 c38 c39 c40 c42
  rcases group19 with ⟨h20,h21,h22,h23,h24,h25,h26,h27,h28,h29⟩
  have group30 := chunk3 a h29 h10 start30 h24 start31 h27 start16 h5 h11 h12 h14 c42 c46 c47 c49 c50 c60 c61
  rcases group30 with ⟨h31,h32,h33,h34,h35,h36,h37⟩
  have group38 := chunk4 a start29 h36 h32 h37 start24 h23 h33 h28 h31 c64 c66 c68 c75 c77 c78
  rcases group38 with ⟨h39,h40,h41,h42,h43⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h4) (And.intro (forced (a 4) 0 start4) (And.intro (forced (a 5) 0 start5) (And.intro (forced (a 6) 0 h7) (And.intro (forced (a 7) 0 h15) (And.intro (forced (a 8) 0 h21) (And.intro (forced (a 9) 0 h3) (And.intro (forced (a 10) 0 h20) (And.intro (forced (a 11) 0 h26) (And.intro (forced (a 12) 0 h10) (And.intro (forced (a 13) 0 h22) (And.intro (forced (a 14) 0 h24) (And.intro (forced (a 15) 0 h27) (And.intro (forced (a 16) 0 h34) (And.intro (forced (a 17) 0 start17) (And.intro (forced (a 18) 0 h5) (And.intro (forced (a 19) 0 start19) (And.intro (forced (a 20) 0 h35) (And.intro (forced (a 21) 0 h36) (And.intro (forced (a 22) 0 h37) (And.intro (forced (a 23) 0 h17) (And.intro (forced (a 24) 0 h41) (And.intro (forced (a 25) 0 h23) (And.intro (forced (a 26) 0 h25) (And.intro (forced (a 27) 0 h28) (And.intro (forced (a 28) 0 h43) (And.intro (forced (a 29) 0 h39) (And.intro (forced (a 30) 0 h40) (forced (a 31) 0 h42)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_176
