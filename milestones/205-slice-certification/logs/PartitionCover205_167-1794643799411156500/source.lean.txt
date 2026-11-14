import FiniteDomain205
namespace PartitionCover205_167
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[15]
def r3 : Array Nat := #[7]
def r4 : Array Nat := #[15]
def r5 : Array Nat := #[1]
def r6 : Array Nat := #[15]
def r7 : Array Nat := #[1]
def r8 : Array Nat := #[15]
def r9 : Array Nat := #[1]
def r10 : Array Nat := #[5]
def r11 : Array Nat := #[15]
def r12 : Array Nat := #[3]
def r13 : Array Nat := #[3]
def r14 : Array Nat := #[15]
def r15 : Array Nat := #[5]
def r16 : Array Nat := #[1,2,4,8]
def r17 : Array Nat := #[1,2,4,8]
def r18 : Array Nat := #[1,2,4,8]
def r19 : Array Nat := #[255,255,255,255]
def r20 : Array Nat := #[1,1,2,2]
def r21 : Array Nat := #[7,56,7,448]
def r22 : Array Nat := #[255,255,255,255]
def r23 : Array Nat := #[1,1,2,2]
def r24 : Array Nat := #[1,2,4,8]
def r25 : Array Nat := #[3,3,12,12]
def r26 : Array Nat := #[3,12]
def r27 : Array Nat := #[3,12]
def r28 : Array Nat := #[1,1,0]
def r29 : Array Nat := #[3,3,2]
def r30 : Array Nat := #[15,0,0]
def r31 : Array Nat := #[453,488,493]
def r32 : Array Nat := #[3]
def r33 : Array Nat := #[321]
def r34 : Array Nat := #[15]
def r35 : Array Nat := #[3,3,0,0]
def r36 : Array Nat := #[1,2,0,2]
def r37 : Array Nat := #[1,1,4,4]
def r38 : Array Nat := #[3,3,12,12]
def r39 : Array Nat := #[1,2,0,2]
def r40 : Array Nat := #[7,56,7,448]
def r41 : Array Nat := #[1,2,4,8]
def r42 : Array Nat := #[1,2,4,8]
def r43 : Array Nat := #[5,4,1,14,12,14,11,3,11]
def r44 : Array Nat := #[5,2,8,5,2,0,5,8,0]
def r45 : Array Nat := #[1,2,4,8]
def r46 : Array Nat := #[3,12,17,96]
def r47 : Array Nat := #[37,16,72,16]
def r48 : Array Nat := #[1,2,4,8]
def r49 : Array Nat := #[1,1,2,2]
def r50 : Array Nat := #[255,255,255,255]
def r51 : Array Nat := #[7,56,7,448]
def r52 : Array Nat := #[1,2,4,8]
def r53 : Array Nat := #[255,255,255,255]
def r54 : Array Nat := #[1,2,4,8]
def r55 : Array Nat := #[3,12]
def r56 : Array Nat := #[3,0]
def r57 : Array Nat := #[3,12]
def r58 : Array Nat := #[3,11,1,0]
def r59 : Array Nat := #[1,2,4,8]
def r60 : Array Nat := #[1,2,4,8,16,32,64,128]
def r61 : Array Nat := #[1,2,1,2,4,8,4,8]
def r62 : Array Nat := #[1,1,2,2,4,4,8,8]
def r63 : Array Nat := #[1,1,2,2,4,4,8,8]
def r64 : Array Nat := #[1,2,1,2,4,8,4,8]
def r65 : Array Nat := #[3,3,12,12]
def r66 : Array Nat := #[5,16,33,2]
def r67 : Array Nat := #[37,16,72,16]
def r68 : Array Nat := #[5,5,5,2,2,2,8,8,8]
def r69 : Array Nat := #[1,4,0,10,4,0,10,1,0]
def r70 : Array Nat := #[3,0,0,3,0,12,0,0,0]
def r71 : Array Nat := #[1,2,4,8]
def r72 : Array Nat := #[5,2,0,2]
def r73 : Array Nat := #[1,2,4,8]
def r74 : Array Nat := #[37,16,72,16]
def r75 : Array Nat := #[3,12,17,96]
def r76 : Array Nat := #[3,3,12,12]
def r77 : Array Nat := #[17,4,3,32]
def r78 : Array Nat := #[49,36,80,88]
def r79 : Array Nat := #[1,10,80,10,4,32,4]
theorem chunk0 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1,2])
    (d9 : a 9 ∈ [0])
    (d10 : a 10 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,2,3,4,5,6,7,8])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 6 ∈ [0,2] ∧ a 19 ∈ [0,2] ∧ a 4 ∈ [0,2] ∧ a 12 ∈ [0,2] ∧ a 14 ∈ [0,2] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0,1] ∧ a 24 ∈ [0,2,4,5,6,7,8] := by
  have b0 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 d2 c10 (by decide +kernel)
  have t0 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b0
  have b1 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t0 b1
  have b2 : a 19 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 1 d3 c15 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b2
  have b3 : a 19 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t3 : a 19 ∈ [0,2] := remove (a 19) 3 [0,2,3] t2 b3
  have b4 : a 4 ≠ 1 := exclude [0,2] (edge r17) (a 4) (a 6) 1 t1 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b4
  have b5 : a 4 ≠ 3 := exclude [0,2] (edge r17) (a 4) (a 6) 3 t1 c17 (by decide +kernel)
  have t5 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t4 b5
  have b6 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r18 v u) (a 12) (a 4) 1 t5 c18 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b6
  have b7 : a 12 ≠ 3 := exclude [0,2] (fun u v => edge r18 v u) (a 12) (a 4) 3 t5 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t6 b7
  have b8 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 1 t1 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b8
  have b9 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r24 v u) (a 14) (a 6) 3 t1 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t8 b9
  have b10 : a 8 ≠ 2 := exclude [0] (edge r28) (a 8) (a 9) 2 d9 c28 (by decide +kernel)
  have t10 : a 8 ∈ [0,1] := remove (a 8) 2 [0,1,2] d8 b10
  have b11 : a 10 ≠ 2 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 2 t10 c29 (by decide +kernel)
  have t11 : a 10 ∈ [0,1,3] := remove (a 10) 2 [0,1,2,3] d10 b11
  have b12 : a 10 ≠ 3 := exclude [0,1] (fun u v => edge r29 v u) (a 10) (a 8) 3 t10 c29 (by decide +kernel)
  have t12 : a 10 ∈ [0,1] := remove (a 10) 3 [0,1,3] t11 b12
  have b13 : a 8 ≠ 1 := exclude [0,2] (edge r30) (a 8) (a 12) 1 t7 c30 (by decide +kernel)
  have t13 : a 8 ∈ [0] := remove (a 8) 1 [0,1] t10 b13
  have b14 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 t13 c31 (by decide +kernel)
  have t14 : a 24 ∈ [0,2,3,4,5,6,7,8] := remove (a 24) 1 [0,1,2,3,4,5,6,7,8] d24 b14
  have b15 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 t13 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,2,4,5,6,7,8] := remove (a 24) 3 [0,2,3,4,5,6,7,8] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t13 (And.intro t12 (t15)))))))

theorem chunk1 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2,4,5,6,7,8])
    (d8 : a 8 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (d10 : a 10 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1,2,3])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    : a 24 ∈ [0,2,6,7,8] ∧ a 11 ∈ [0,1] ∧ a 13 ∈ [0,6,8] ∧ a 10 ∈ [0] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0,1,3] := by
  have b0 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,5,6,7,8] := remove (a 24) 4 [0,2,4,5,6,7,8] d24 b0
  have b1 : a 24 ≠ 5 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 5 d8 c31 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,6,7,8] := remove (a 24) 5 [0,2,5,6,7,8] t0 b1
  have b2 : a 11 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 2 d9 c32 (by decide +kernel)
  have t2 : a 11 ∈ [0,1,3] := remove (a 11) 2 [0,1,2,3] d11 b2
  have b3 : a 11 ≠ 3 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 3 d9 c32 (by decide +kernel)
  have t3 : a 11 ∈ [0,1] := remove (a 11) 3 [0,1,3] t2 b3
  have b4 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0,2,3,4,5,6,7,8] := remove (a 13) 1 [0,1,2,3,4,5,6,7,8] d13 b4
  have b5 : a 13 ≠ 2 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t5 : a 13 ∈ [0,3,4,5,6,7,8] := remove (a 13) 2 [0,2,3,4,5,6,7,8] t4 b5
  have b6 : a 13 ≠ 3 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t6 : a 13 ∈ [0,4,5,6,7,8] := remove (a 13) 3 [0,3,4,5,6,7,8] t5 b6
  have b7 : a 13 ≠ 4 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t7 : a 13 ∈ [0,5,6,7,8] := remove (a 13) 4 [0,4,5,6,7,8] t6 b7
  have b8 : a 13 ≠ 5 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t8 : a 13 ∈ [0,6,7,8] := remove (a 13) 5 [0,5,6,7,8] t7 b8
  have b9 : a 13 ≠ 7 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 7 d9 c33 (by decide +kernel)
  have t9 : a 13 ∈ [0,6,8] := remove (a 13) 7 [0,6,7,8] t8 b9
  have b10 : a 10 ≠ 1 := exclude [0,2] (edge r36) (a 10) (a 14) 1 d14 c36 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b10
  have b11 : a 14 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 2 t10 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b11
  have b12 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t10 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b12
  have b13 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t10 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,3] := remove (a 26) 2 [0,2,3] t12 b13
  have b14 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t10 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0] := remove (a 26) 3 [0,3] t13 b14
  have b15 : a 15 ≠ 2 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 2 t3 c38 (by decide +kernel)
  have t15 : a 15 ∈ [0,1,3] := remove (a 15) 2 [0,1,2,3] d15 b15
  exact And.intro t1 (And.intro t3 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t14 (t15))))))

theorem chunk2 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,3])
    (d11 : a 11 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,6,8])
    (d12 : a 12 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d28 : a 28 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1,2,3,4,5,6])
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    : a 15 ∈ [0] ∧ a 27 ∈ [0,1] ∧ a 13 ∈ [0] ∧ a 12 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0,2] ∧ a 30 ∈ [0,1,6] := by
  have b0 : a 15 ≠ 3 := exclude [0,1] (fun u v => edge r38 v u) (a 15) (a 11) 3 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [0,1] := remove (a 15) 3 [0,1,3] d15 b0
  have b1 : a 27 ≠ 2 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,1,3] := remove (a 27) 2 [0,1,2,3] d27 b1
  have b2 : a 27 ≠ 3 := exclude [0,1] (fun u v => edge r39 v u) (a 27) (a 11) 3 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,1] := remove (a 27) 3 [0,1,3] t1 b2
  have b3 : a 13 ≠ 6 := exclude [0,2] (fun u v => edge r40 v u) (a 13) (a 12) 6 d12 c40 (by decide +kernel)
  have t3 : a 13 ∈ [0,8] := remove (a 13) 6 [0,6,8] d13 b3
  have b4 : a 13 ≠ 8 := exclude [0,2] (fun u v => edge r40 v u) (a 13) (a 12) 8 d12 c40 (by decide +kernel)
  have t4 : a 13 ∈ [0] := remove (a 13) 8 [0,8] t3 b4
  have b5 : a 12 ≠ 2 := exclude [0] (edge r41) (a 12) (a 14) 2 d14 c41 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b5
  have b6 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t5 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b6
  have b7 : a 28 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 2 t5 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,3] := remove (a 28) 2 [0,2,3] t6 b7
  have b8 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 t5 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0] := remove (a 28) 3 [0,3] t7 b8
  have b9 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 t4 c43 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 1 [0,1] t0 b9
  have b10 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 t4 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b10
  have b11 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 t4 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t10 b11
  have b12 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,3,4,5,6] := remove (a 30) 2 [0,1,2,3,4,5,6] d30 b12
  have b13 : a 30 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 3 d14 c46 (by decide +kernel)
  have t13 : a 30 ∈ [0,1,4,5,6] := remove (a 30) 3 [0,1,3,4,5,6] t12 b13
  have b14 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 d14 c46 (by decide +kernel)
  have t14 : a 30 ∈ [0,1,5,6] := remove (a 30) 4 [0,1,4,5,6] t13 b14
  have b15 : a 30 ≠ 5 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 5 d14 c46 (by decide +kernel)
  have t15 : a 30 ∈ [0,1,6] := remove (a 30) 5 [0,1,5,6] t14 b15
  exact And.intro t9 (And.intro t2 (And.intro t4 (And.intro t5 (And.intro t8 (And.intro t11 (t15))))))

theorem chunk3 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,6])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3,4,5,6])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,2,6,7,8])
    (d17 : a 17 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,2])
    (d25 : a 25 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,1,2,3])
    (d27 : a 27 ∈ [0,1])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 30 ∈ [0,1] ∧ a 31 ∈ [0,2,5] ∧ a 16 ∈ [0,2,3] ∧ a 17 ∈ [0,2] ∧ a 25 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 22 ∈ [0,1] ∧ a 23 ∈ [0,1] ∧ a 19 ∈ [0] := by
  have b0 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1] := remove (a 30) 6 [0,1,6] d30 b0
  have b1 : a 31 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,2,3,4,5,6] := remove (a 31) 1 [0,1,2,3,4,5,6] d31 b1
  have b2 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0,2,4,5,6] := remove (a 31) 3 [0,2,3,4,5,6] t1 b2
  have b3 : a 31 ≠ 4 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 4 d15 c47 (by decide +kernel)
  have t3 : a 31 ∈ [0,2,5,6] := remove (a 31) 4 [0,2,4,5,6] t2 b3
  have b4 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 d15 c47 (by decide +kernel)
  have t4 : a 31 ∈ [0,2,5] := remove (a 31) 6 [0,2,5,6] t3 b4
  have b5 : a 16 ≠ 1 := exclude [0,2,6,7,8] (edge r51) (a 16) (a 24) 1 d24 c51 (by decide +kernel)
  have t5 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b5
  have b6 : a 17 ≠ 1 := exclude [0,2] (edge r52) (a 17) (a 19) 1 d19 c52 (by decide +kernel)
  have t6 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b6
  have b7 : a 17 ≠ 3 := exclude [0,2] (edge r52) (a 17) (a 19) 3 d19 c52 (by decide +kernel)
  have t7 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t6 b7
  have b8 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 1 t7 c54 (by decide +kernel)
  have t8 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b8
  have b9 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r54 v u) (a 25) (a 17) 3 t7 c54 (by decide +kernel)
  have t9 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0,1,2,3] (edge r56) (a 18) (a 22) 1 d22 c56 (by decide +kernel)
  have t10 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b10
  have b11 : a 22 ≠ 2 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 2 t10 c56 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,3] := remove (a 22) 2 [0,1,2,3] d22 b11
  have b12 : a 22 ≠ 3 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 3 t10 c56 (by decide +kernel)
  have t12 : a 22 ∈ [0,1] := remove (a 22) 3 [0,1,3] t11 b12
  have b13 : a 23 ≠ 2 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 2 d19 c58 (by decide +kernel)
  have t13 : a 23 ∈ [0,1,3] := remove (a 23) 2 [0,1,2,3] d23 b13
  have b14 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r58 v u) (a 23) (a 19) 3 d19 c58 (by decide +kernel)
  have t14 : a 23 ∈ [0,1] := remove (a 23) 3 [0,1,3] t13 b14
  have b15 : a 19 ≠ 2 := exclude [0,1] (edge r59) (a 19) (a 27) 2 d27 c59 (by decide +kernel)
  have t15 : a 19 ∈ [0] := remove (a 19) 2 [0,2] d19 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk4 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d20 : a 20 ∈ [0,1,2,3,4,5,6,7])
    (d22 : a 22 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (d23 : a 23 ∈ [0,1])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0,1])
    (c59 : edge r59 (a 19) (a 27)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    : a 27 ∈ [0] ∧ a 20 ∈ [0,1] ∧ a 21 ∈ [0,2] ∧ a 29 ∈ [0] ∧ a 22 ∈ [0] ∧ a 30 ∈ [0] := by
  have b0 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 d19 c59 (by decide +kernel)
  have t0 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b0
  have b1 : a 20 ≠ 4 := exclude [0,1] (edge r61) (a 20) (a 22) 4 d22 c61 (by decide +kernel)
  have t1 : a 20 ∈ [0,1,2,3,5,6,7] := remove (a 20) 4 [0,1,2,3,4,5,6,7] d20 b1
  have b2 : a 20 ≠ 5 := exclude [0,1] (edge r61) (a 20) (a 22) 5 d22 c61 (by decide +kernel)
  have t2 : a 20 ∈ [0,1,2,3,6,7] := remove (a 20) 5 [0,1,2,3,5,6,7] t1 b2
  have b3 : a 20 ≠ 6 := exclude [0,1] (edge r61) (a 20) (a 22) 6 d22 c61 (by decide +kernel)
  have t3 : a 20 ∈ [0,1,2,3,7] := remove (a 20) 6 [0,1,2,3,6,7] t2 b3
  have b4 : a 20 ≠ 7 := exclude [0,1] (edge r61) (a 20) (a 22) 7 d22 c61 (by decide +kernel)
  have t4 : a 20 ∈ [0,1,2,3] := remove (a 20) 7 [0,1,2,3,7] t3 b4
  have b5 : a 20 ≠ 2 := exclude [0] (edge r62) (a 20) (a 28) 2 d28 c62 (by decide +kernel)
  have t5 : a 20 ∈ [0,1,3] := remove (a 20) 2 [0,1,2,3] t4 b5
  have b6 : a 20 ≠ 3 := exclude [0] (edge r62) (a 20) (a 28) 3 d28 c62 (by decide +kernel)
  have t6 : a 20 ∈ [0,1] := remove (a 20) 3 [0,1,3] t5 b6
  have b7 : a 21 ≠ 4 := exclude [0,1] (edge r63) (a 21) (a 23) 4 d23 c63 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,2,3,5,6,7] := remove (a 21) 4 [0,1,2,3,4,5,6,7] d21 b7
  have b8 : a 21 ≠ 5 := exclude [0,1] (edge r63) (a 21) (a 23) 5 d23 c63 (by decide +kernel)
  have t8 : a 21 ∈ [0,1,2,3,6,7] := remove (a 21) 5 [0,1,2,3,5,6,7] t7 b8
  have b9 : a 21 ≠ 6 := exclude [0,1] (edge r63) (a 21) (a 23) 6 d23 c63 (by decide +kernel)
  have t9 : a 21 ∈ [0,1,2,3,7] := remove (a 21) 6 [0,1,2,3,6,7] t8 b9
  have b10 : a 21 ≠ 7 := exclude [0,1] (edge r63) (a 21) (a 23) 7 d23 c63 (by decide +kernel)
  have t10 : a 21 ∈ [0,1,2,3] := remove (a 21) 7 [0,1,2,3,7] t9 b10
  have b11 : a 21 ≠ 1 := exclude [0,2] (edge r64) (a 21) (a 29) 1 d29 c64 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] t10 b11
  have b12 : a 21 ≠ 3 := exclude [0,2] (edge r64) (a 21) (a 29) 3 d29 c64 (by decide +kernel)
  have t12 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] t11 b12
  have b13 : a 29 ≠ 2 := exclude [0,2] (fun u v => edge r64 v u) (a 29) (a 21) 2 t12 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b13
  have b14 : a 22 ≠ 1 := exclude [0,1] (edge r66) (a 22) (a 30) 1 d30 c66 (by decide +kernel)
  have t14 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b14
  have b15 : a 30 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 1 t14 c66 (by decide +kernel)
  have t15 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b15
  exact And.intro t0 (And.intro t6 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))

theorem chunk5 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1])
    (d31 : a 31 ∈ [0,2,5])
    (d24 : a 24 ∈ [0,2,6,7,8])
    (d25 : a 25 ∈ [0,2])
    (d26 : a 26 ∈ [0])
    (d27 : a 27 ∈ [0])
    (d5 : a 5 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,2])
    (d12 : a 12 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d7 : a 7 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d11 : a 11 ∈ [0,1])
    (d16 : a 16 ∈ [0,2,3])
    (d17 : a 17 ∈ [0,2])
    (d18 : a 18 ∈ [0])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 23 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 31 ∈ [0] ∧ a 5 ∈ [0,2] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 23 ≠ 1 := exclude [0,2,5] (edge r67) (a 23) (a 31) 1 d31 c67 (by decide +kernel)
  have t0 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b0
  have b1 : a 24 ≠ 6 := exclude [0,2] (edge r68) (a 24) (a 25) 6 d25 c68 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,7,8] := remove (a 24) 6 [0,2,6,7,8] d24 b1
  have b2 : a 24 ≠ 7 := exclude [0,2] (edge r68) (a 24) (a 25) 7 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0,2,8] := remove (a 24) 7 [0,2,7,8] t1 b2
  have b3 : a 24 ≠ 8 := exclude [0,2] (edge r68) (a 24) (a 25) 8 d25 c68 (by decide +kernel)
  have t3 : a 24 ∈ [0,2] := remove (a 24) 8 [0,2,8] t2 b3
  have b4 : a 24 ≠ 2 := exclude [0] (edge r69) (a 24) (a 26) 2 d26 c69 (by decide +kernel)
  have t4 : a 24 ∈ [0] := remove (a 24) 2 [0,2] t3 b4
  have b5 : a 25 ≠ 2 := exclude [0] (edge r71) (a 25) (a 27) 2 d27 c71 (by decide +kernel)
  have t5 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b5
  have b6 : a 31 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 2 d27 c75 (by decide +kernel)
  have t6 : a 31 ∈ [0,5] := remove (a 31) 2 [0,2,5] d31 b6
  have b7 : a 31 ≠ 5 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 5 d27 c75 (by decide +kernel)
  have t7 : a 31 ∈ [0] := remove (a 31) 5 [0,5] t6 b7
  have b8 : a 5 ≠ 1 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t8 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b8
  have b9 : a 5 ≠ 3 := exclude [0,2] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t9 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t8 b9
  have b10 : a 4 ≠ 2 := exclude [0] (edge r18) (a 4) (a 12) 2 d12 c18 (by decide +kernel)
  have t10 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b10
  have b11 : a 6 ≠ 2 := exclude [0] (edge r24) (a 6) (a 14) 2 d14 c24 (by decide +kernel)
  have t11 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b11
  have b12 : a 7 ≠ 1 := exclude [0] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t12 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b12
  have b13 : a 11 ≠ 1 := exclude [0] (edge r39) (a 11) (a 27) 1 d27 c39 (by decide +kernel)
  have t13 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b13
  have b14 : a 16 ≠ 3 := exclude [0,2] (edge r48) (a 16) (a 17) 3 d17 c48 (by decide +kernel)
  have t14 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] d16 b14
  have b15 : a 16 ≠ 2 := exclude [0] (edge r49) (a 16) (a 18) 2 d18 c49 (by decide +kernel)
  have t15 : a 16 ∈ [0] := remove (a 16) 2 [0,2] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (t15)))))))))

theorem chunk6 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,2])
    (d19 : a 19 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d5 : a 5 ∈ [0,2])
    (d4 : a 4 ∈ [0])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 17 ∈ [0] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 17 ≠ 2 := exclude [0] (edge r52) (a 17) (a 19) 2 d19 c52 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b0
  have b1 : a 20 ≠ 1 := exclude [0,2] (edge r60) (a 20) (a 21) 1 d21 c60 (by decide +kernel)
  have t1 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b1
  have b2 : a 21 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 2 t1 c60 (by decide +kernel)
  have t2 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b2
  have b3 : a 5 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 2 d4 c16 (by decide +kernel)
  have t3 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b3
  exact And.intro t0 (And.intro t1 (And.intro t2 (t3)))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1,2,3])
    (start5 : a 5 ∈ [0,1,2,3])
    (start6 : a 6 ∈ [0,1,2,3])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1,2])
    (start9 : a 9 ∈ [0])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1,2,3])
    (start13 : a 13 ∈ [0,1,2,3,4,5,6,7,8])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1,2,3])
    (start16 : a 16 ∈ [0,1,2,3])
    (start17 : a 17 ∈ [0,1,2,3])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1,2,3])
    (start20 : a 20 ∈ [0,1,2,3,4,5,6,7])
    (start21 : a 21 ∈ [0,1,2,3,4,5,6,7])
    (start22 : a 22 ∈ [0,1,2,3])
    (start23 : a 23 ∈ [0,1,2,3])
    (start24 : a 24 ∈ [0,1,2,3,4,5,6,7,8])
    (start25 : a 25 ∈ [0,1,2,3])
    (start26 : a 26 ∈ [0,1,2,3])
    (start27 : a 27 ∈ [0,1,2,3])
    (start28 : a 28 ∈ [0,1,2,3])
    (start29 : a 29 ∈ [0,1,2,3])
    (start30 : a 30 ∈ [0,1,2,3,4,5,6])
    (start31 : a 31 ∈ [0,1,2,3,4,5,6])
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
  have group1 := chunk0 a start6 start2 start19 start3 start4 start12 start14 start8 start9 start10 start24 c10 c15 c17 c18 c24 c28 c29 c30 c31
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8,h9⟩
  have group10 := chunk1 a h9 h7 start11 start9 start13 h8 h6 start26 start15 c31 c32 c33 c36 c37 c38
  rcases group10 with ⟨h11,h12,h13,h14,h15,h16,h17⟩
  have group18 := chunk2 a h17 h12 start27 h13 h5 h15 start28 start29 start30 c38 c39 c40 c41 c42 c43 c44 c46
  rcases group18 with ⟨h19,h20,h21,h22,h23,h24,h25⟩
  have group26 := chunk3 a h25 h15 start31 h19 start16 h11 start17 h3 start25 start18 start22 start23 h20 c46 c47 c51 c52 c54 c56 c58 c59
  rcases group26 with ⟨h27,h28,h29,h30,h31,h32,h33,h34,h35⟩
  have group36 := chunk4 a h20 h35 start20 h33 h23 start21 h34 h24 h27 c59 c61 c62 c63 c64 c66
  rcases group36 with ⟨h37,h38,h39,h40,h41,h42⟩
  have group43 := chunk5 a h34 h28 h11 h31 h16 h37 start5 h4 h22 h2 h15 start7 h19 h12 h29 h30 h32 c16 c18 c24 c26 c39 c48 c49 c67 c68 c69 c71 c75
  rcases group43 with ⟨h44,h45,h46,h47,h48,h49,h50,h51,h52,h53⟩
  have group54 := chunk6 a h30 h35 h38 h39 h48 h49 c16 c52 c60
  rcases group54 with ⟨h55,h56,h57,h58⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h49) (And.intro (forced (a 5) 0 h58) (And.intro (forced (a 6) 0 h50) (And.intro (forced (a 7) 0 h51) (And.intro (forced (a 8) 0 h7) (And.intro (forced (a 9) 0 start9) (And.intro (forced (a 10) 0 h14) (And.intro (forced (a 11) 0 h52) (And.intro (forced (a 12) 0 h22) (And.intro (forced (a 13) 0 h21) (And.intro (forced (a 14) 0 h15) (And.intro (forced (a 15) 0 h19) (And.intro (forced (a 16) 0 h53) (And.intro (forced (a 17) 0 h55) (And.intro (forced (a 18) 0 h32) (And.intro (forced (a 19) 0 h35) (And.intro (forced (a 20) 0 h56) (And.intro (forced (a 21) 0 h57) (And.intro (forced (a 22) 0 h41) (And.intro (forced (a 23) 0 h44) (And.intro (forced (a 24) 0 h45) (And.intro (forced (a 25) 0 h46) (And.intro (forced (a 26) 0 h16) (And.intro (forced (a 27) 0 h37) (And.intro (forced (a 28) 0 h23) (And.intro (forced (a 29) 0 h40) (And.intro (forced (a 30) 0 h42) (forced (a 31) 0 h47)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_167
