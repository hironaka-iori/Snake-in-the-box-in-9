import FiniteDomain205
namespace PartitionCover205_245
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[5]
def r5 : Array Nat := #[5]
def r6 : Array Nat := #[5]
def r7 : Array Nat := #[1,2]
def r8 : Array Nat := #[1,2]
def r9 : Array Nat := #[1,2]
def r10 : Array Nat := #[1,2]
def r11 : Array Nat := #[1,2]
def r12 : Array Nat := #[3,12]
def r13 : Array Nat := #[1,2]
def r14 : Array Nat := #[3,3]
def r15 : Array Nat := #[1,2]
def r16 : Array Nat := #[1,2]
def r17 : Array Nat := #[1,2]
def r18 : Array Nat := #[1,1]
def r19 : Array Nat := #[1,1,2,2]
def r20 : Array Nat := #[1,2,1,2]
def r21 : Array Nat := #[1,2,1,2]
def r22 : Array Nat := #[1,2,1,2]
def r23 : Array Nat := #[1,2,1,2]
def r24 : Array Nat := #[1,1,2,2]
def r25 : Array Nat := #[1,2,1,2]
def r26 : Array Nat := #[1,2]
def r27 : Array Nat := #[5,10]
def r28 : Array Nat := #[5,10]
def r29 : Array Nat := #[3,3]
def r30 : Array Nat := #[3,3]
def r31 : Array Nat := #[1,2]
def r32 : Array Nat := #[1,2]
def r33 : Array Nat := #[3,3]
def r34 : Array Nat := #[1,2]
def r35 : Array Nat := #[1,2]
def r36 : Array Nat := #[3,3]
def r37 : Array Nat := #[3,3]
def r38 : Array Nat := #[1,2]
def r39 : Array Nat := #[3,3]
def r40 : Array Nat := #[3,3]
def r41 : Array Nat := #[1,1,2,2]
def r42 : Array Nat := #[1,1,2,2]
def r43 : Array Nat := #[1,2,1,2]
def r44 : Array Nat := #[1,2,1,2]
def r45 : Array Nat := #[1,1,2,2]
def r46 : Array Nat := #[1,2,1,2]
def r47 : Array Nat := #[1,2,1,2]
def r48 : Array Nat := #[3,3]
def r49 : Array Nat := #[5,10]
def r50 : Array Nat := #[5,10]
def r51 : Array Nat := #[1,1,2,2]
def r52 : Array Nat := #[1,2,1,2]
def r53 : Array Nat := #[1,1,2,2]
def r54 : Array Nat := #[1,2,4,8]
def r55 : Array Nat := #[3,3]
def r56 : Array Nat := #[3,3]
def r57 : Array Nat := #[5,10]
def r58 : Array Nat := #[1,2]
def r59 : Array Nat := #[3,3]
def r60 : Array Nat := #[1,2]
def r61 : Array Nat := #[1,2]
def r62 : Array Nat := #[1,2,1,2]
def r63 : Array Nat := #[1,1,2,2]
def r64 : Array Nat := #[1,1,2,2]
def r65 : Array Nat := #[1,2,1,2]
def r66 : Array Nat := #[3,12]
def r67 : Array Nat := #[1,2]
def r68 : Array Nat := #[5,10]
def r69 : Array Nat := #[5,10]
def r70 : Array Nat := #[1,2]
def r71 : Array Nat := #[5,10]
def r72 : Array Nat := #[1,1,2,2]
def r73 : Array Nat := #[1,2,1,2]
def r74 : Array Nat := #[3,3]
def r75 : Array Nat := #[1,2]
def r76 : Array Nat := #[3,3]
def r77 : Array Nat := #[1,2]
def r78 : Array Nat := #[3,3]
def r79 : Array Nat := #[3,3]
def r80 : Array Nat := #[1,2]
def r81 : Array Nat := #[3,3]
def r82 : Array Nat := #[1,1,2,2]
def r83 : Array Nat := #[1,2,1,2]
def r84 : Array Nat := #[1,2,4,8]
def r85 : Array Nat := #[1,2,1,2]
def r86 : Array Nat := #[3,3]
def r87 : Array Nat := #[5,10]
def r88 : Array Nat := #[1,1,2,2]
def r89 : Array Nat := #[1,2,1,2]
def r90 : Array Nat := #[1,1,2,2]
def r91 : Array Nat := #[1,2,1,2]
def r92 : Array Nat := #[3,12]
def r93 : Array Nat := #[1,2]
def r94 : Array Nat := #[5,10]
def r95 : Array Nat := #[1,1,2,2]
def r96 : Array Nat := #[1,2,1,2]
def r97 : Array Nat := #[3,3]
def r98 : Array Nat := #[3,3]
def r99 : Array Nat := #[3,3]
def r100 : Array Nat := #[1,2]
def r101 : Array Nat := #[3,3]
def r102 : Array Nat := #[1,2]
def r103 : Array Nat := #[3,3]
def r104 : Array Nat := #[3,3]
def r105 : Array Nat := #[1,1,2,2]
def r106 : Array Nat := #[1,2,4,8]
def r107 : Array Nat := #[1,2,1,2]
def r108 : Array Nat := #[5,10]
def r109 : Array Nat := #[5,10]
def r110 : Array Nat := #[1,1,2,2]
def r111 : Array Nat := #[1,2,1,2]
def r112 : Array Nat := #[1,4,2,8]
def r113 : Array Nat := #[1,2,1,2]
def r114 : Array Nat := #[1,1,2,2]
def r115 : Array Nat := #[1,2,1,2]
def r116 : Array Nat := #[3,3]
def r117 : Array Nat := #[5,10]
def r118 : Array Nat := #[3,12]
def r119 : Array Nat := #[1,2]
def r120 : Array Nat := #[1,1,2,2]
def r121 : Array Nat := #[1,1,2,2]
def r122 : Array Nat := #[1,2,1,2]
def r123 : Array Nat := #[1,2,1,2]
def r124 : Array Nat := #[1,2]
def r125 : Array Nat := #[3,3]
def r126 : Array Nat := #[3,3]
def r127 : Array Nat := #[1,2]
def r128 : Array Nat := #[1,2]
theorem chunk0 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d0 : a 0 ∈ [0])
    (d6 : a 6 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 3)=true)
    (c4 : edge r4 (a 1) (a 6)=true)
    (c5 : edge r5 (a 1) (a 13)=true)
    (c6 : edge r6 (a 1) (a 28)=true)
    (c10 : edge r10 (a 3) (a 4)=true)
    (c11 : edge r11 (a 3) (a 9)=true)
    (c12 : edge r12 (a 3) (a 16)=true)
    (c13 : edge r13 (a 4) (a 5)=true)
    (c15 : edge r15 (a 4) (a 17)=true)
    (c16 : edge r16 (a 4) (a 30)=true)
    (c17 : edge r17 (a 5) (a 12)=true)
    (c18 : edge r18 (a 5) (a 19)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0,2] ∧ a 13 ∈ [0,2] ∧ a 28 ∈ [0,2] ∧ a 4 ∈ [0] ∧ a 9 ∈ [0] ∧ a 16 ∈ [0,1] ∧ a 5 ∈ [0] ∧ a 17 ∈ [0] ∧ a 30 ∈ [0] ∧ a 12 ∈ [0] ∧ a 19 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 3) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 6) (a 1) 1 d1 c4 (by decide +kernel)
  have t1 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b1
  have b2 : a 6 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 6) (a 1) 3 d1 c4 (by decide +kernel)
  have t2 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t1 b2
  have b3 : a 13 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 13) (a 1) 1 d1 c5 (by decide +kernel)
  have t3 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b3
  have b4 : a 13 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 13) (a 1) 3 d1 c5 (by decide +kernel)
  have t4 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t3 b4
  have b5 : a 28 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 28) (a 1) 1 d1 c6 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b5
  have b6 : a 28 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 28) (a 1) 3 d1 c6 (by decide +kernel)
  have t6 : a 28 ∈ [0,2] := remove (a 28) 3 [0,2,3] t5 b6
  have b7 : a 4 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 4) (a 3) 1 t0 c10 (by decide +kernel)
  have t7 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b7
  have b8 : a 9 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 9) (a 3) 1 t0 c11 (by decide +kernel)
  have t8 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b8
  have b9 : a 16 ≠ 2 := exclude [0] (fun u v => edge r12 v u) (a 16) (a 3) 2 t0 c12 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,3] := remove (a 16) 2 [0,1,2,3] d16 b9
  have b10 : a 16 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 16) (a 3) 3 t0 c12 (by decide +kernel)
  have t10 : a 16 ∈ [0,1] := remove (a 16) 3 [0,1,3] t9 b10
  have b11 : a 5 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 5) (a 4) 1 t7 c13 (by decide +kernel)
  have t11 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b11
  have b12 : a 17 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 17) (a 4) 1 t7 c15 (by decide +kernel)
  have t12 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b12
  have b13 : a 30 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 30) (a 4) 1 t7 c16 (by decide +kernel)
  have t13 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b13
  have b14 : a 12 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 12) (a 5) 1 t11 c17 (by decide +kernel)
  have t14 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b14
  have b15 : a 19 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 19) (a 5) 1 t11 c18 (by decide +kernel)
  have t15 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))

theorem chunk1 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1])
    (d6 : a 6 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d33 : a 33 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d35 : a 35 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d17 : a 17 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d41 : a 41 ∈ [0,1,2,3])
    (c20 : edge r20 (a 6) (a 10)=true)
    (c21 : edge r21 (a 6) (a 21)=true)
    (c22 : edge r22 (a 6) (a 33)=true)
    (c26 : edge r26 (a 8) (a 12)=true)
    (c27 : edge r27 (a 8) (a 23)=true)
    (c28 : edge r28 (a 8) (a 34)=true)
    (c31 : edge r31 (a 9) (a 24)=true)
    (c32 : edge r32 (a 9) (a 35)=true)
    (c34 : edge r34 (a 10) (a 25)=true)
    (c35 : edge r35 (a 10) (a 36)=true)
    (c42 : edge r42 (a 13) (a 17)=true)
    (c49 : edge r49 (a 15) (a 23)=true)
    (c50 : edge r50 (a 15) (a 41)=true)
    : a 10 ∈ [0] ∧ a 21 ∈ [0] ∧ a 33 ∈ [0] ∧ a 8 ∈ [0] ∧ a 23 ∈ [0,2] ∧ a 34 ∈ [0,2] ∧ a 24 ∈ [0] ∧ a 35 ∈ [0] ∧ a 25 ∈ [0] ∧ a 36 ∈ [0] ∧ a 13 ∈ [0] ∧ a 15 ∈ [0] ∧ a 41 ∈ [0,2] := by
  have b0 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r20 v u) (a 10) (a 6) 1 d6 c20 (by decide +kernel)
  have t0 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b0
  have b1 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r21 v u) (a 21) (a 6) 1 d6 c21 (by decide +kernel)
  have t1 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b1
  have b2 : a 33 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 33) (a 6) 1 d6 c22 (by decide +kernel)
  have t2 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b2
  have b3 : a 8 ≠ 1 := exclude [0] (edge r26) (a 8) (a 12) 1 d12 c26 (by decide +kernel)
  have t3 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b3
  have b4 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 8) 1 t3 c27 (by decide +kernel)
  have t4 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b4
  have b5 : a 23 ≠ 3 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 8) 3 t3 c27 (by decide +kernel)
  have t5 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t4 b5
  have b6 : a 34 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 34) (a 8) 1 t3 c28 (by decide +kernel)
  have t6 : a 34 ∈ [0,2,3] := remove (a 34) 1 [0,1,2,3] d34 b6
  have b7 : a 34 ≠ 3 := exclude [0] (fun u v => edge r28 v u) (a 34) (a 8) 3 t3 c28 (by decide +kernel)
  have t7 : a 34 ∈ [0,2] := remove (a 34) 3 [0,2,3] t6 b7
  have b8 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 9) 1 d9 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b8
  have b9 : a 35 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 35) (a 9) 1 d9 c32 (by decide +kernel)
  have t9 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b9
  have b10 : a 25 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 10) 1 t0 c34 (by decide +kernel)
  have t10 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b10
  have b11 : a 36 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 36) (a 10) 1 t0 c35 (by decide +kernel)
  have t11 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b11
  have b12 : a 13 ≠ 2 := exclude [0] (edge r42) (a 13) (a 17) 2 d17 c42 (by decide +kernel)
  have t12 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b12
  have b13 : a 15 ≠ 1 := exclude [0,2] (edge r49) (a 15) (a 23) 1 t5 c49 (by decide +kernel)
  have t13 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b13
  have b14 : a 41 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 41) (a 15) 1 t13 c50 (by decide +kernel)
  have t14 : a 41 ∈ [0,2,3] := remove (a 41) 1 [0,1,2,3] d41 b14
  have b15 : a 41 ≠ 3 := exclude [0] (fun u v => edge r50 v u) (a 41) (a 15) 3 t13 c50 (by decide +kernel)
  have t15 : a 41 ∈ [0,2] := remove (a 41) 3 [0,2,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (t15))))))))))))

theorem chunk2 (a : Nat → Nat)
    (d42 : a 42 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,1])
    (d43 : a 43 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0])
    (d18 : a 18 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d27 : a 27 ∈ [0,1])
    (d44 : a 44 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0])
    (d24 : a 24 ∈ [0])
    (d45 : a 45 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d46 : a 46 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (c54 : edge r54 (a 16) (a 42)=true)
    (c57 : edge r57 (a 17) (a 43)=true)
    (c58 : edge r58 (a 18) (a 19)=true)
    (c60 : edge r60 (a 19) (a 27)=true)
    (c61 : edge r61 (a 19) (a 44)=true)
    (c62 : edge r62 (a 20) (a 21)=true)
    (c64 : edge r64 (a 20) (a 24)=true)
    (c65 : edge r65 (a 20) (a 45)=true)
    (c66 : edge r66 (a 21) (a 23)=true)
    (c68 : edge r68 (a 21) (a 46)=true)
    (c69 : edge r69 (a 22) (a 23)=true)
    (c70 : edge r70 (a 22) (a 26)=true)
    : a 42 ∈ [0,1] ∧ a 43 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 27 ∈ [0] ∧ a 44 ∈ [0] ∧ a 20 ∈ [0] ∧ a 45 ∈ [0] ∧ a 23 ∈ [0] ∧ a 46 ∈ [0,2] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 42 ≠ 2 := exclude [0,1] (fun u v => edge r54 v u) (a 42) (a 16) 2 d16 c54 (by decide +kernel)
  have t0 : a 42 ∈ [0,1,3] := remove (a 42) 2 [0,1,2,3] d42 b0
  have b1 : a 42 ≠ 3 := exclude [0,1] (fun u v => edge r54 v u) (a 42) (a 16) 3 d16 c54 (by decide +kernel)
  have t1 : a 42 ∈ [0,1] := remove (a 42) 3 [0,1,3] t0 b1
  have b2 : a 43 ≠ 1 := exclude [0] (fun u v => edge r57 v u) (a 43) (a 17) 1 d17 c57 (by decide +kernel)
  have t2 : a 43 ∈ [0,2,3] := remove (a 43) 1 [0,1,2,3] d43 b2
  have b3 : a 43 ≠ 3 := exclude [0] (fun u v => edge r57 v u) (a 43) (a 17) 3 d17 c57 (by decide +kernel)
  have t3 : a 43 ∈ [0,2] := remove (a 43) 3 [0,2,3] t2 b3
  have b4 : a 18 ≠ 1 := exclude [0] (edge r58) (a 18) (a 19) 1 d19 c58 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b4
  have b5 : a 27 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 27) (a 19) 1 d19 c60 (by decide +kernel)
  have t5 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b5
  have b6 : a 44 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 44) (a 19) 1 d19 c61 (by decide +kernel)
  have t6 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b6
  have b7 : a 20 ≠ 1 := exclude [0] (edge r62) (a 20) (a 21) 1 d21 c62 (by decide +kernel)
  have t7 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b7
  have b8 : a 20 ≠ 3 := exclude [0] (edge r62) (a 20) (a 21) 3 d21 c62 (by decide +kernel)
  have t8 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t7 b8
  have b9 : a 20 ≠ 2 := exclude [0] (edge r64) (a 20) (a 24) 2 d24 c64 (by decide +kernel)
  have t9 : a 20 ∈ [0] := remove (a 20) 2 [0,2] t8 b9
  have b10 : a 45 ≠ 1 := exclude [0] (fun u v => edge r65 v u) (a 45) (a 20) 1 t9 c65 (by decide +kernel)
  have t10 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b10
  have b11 : a 23 ≠ 2 := exclude [0] (fun u v => edge r66 v u) (a 23) (a 21) 2 d21 c66 (by decide +kernel)
  have t11 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b11
  have b12 : a 46 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 46) (a 21) 1 d21 c68 (by decide +kernel)
  have t12 : a 46 ∈ [0,2,3] := remove (a 46) 1 [0,1,2,3] d46 b12
  have b13 : a 46 ≠ 3 := exclude [0] (fun u v => edge r68 v u) (a 46) (a 21) 3 d21 c68 (by decide +kernel)
  have t13 : a 46 ∈ [0,2] := remove (a 46) 3 [0,2,3] t12 b13
  have b14 : a 22 ≠ 1 := exclude [0] (edge r69) (a 22) (a 23) 1 t11 c69 (by decide +kernel)
  have t14 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b14
  have b15 : a 26 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 26) (a 22) 1 t14 c70 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))))))))

theorem chunk3 (a : Nat → Nat)
    (d47 : a 47 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0])
    (d48 : a 48 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d51 : a 51 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d28 : a 28 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d32 : a 32 ∈ [0,1,2,3])
    (d33 : a 33 ∈ [0])
    (d35 : a 35 ∈ [0])
    (d34 : a 34 ∈ [0,2])
    (d38 : a 38 ∈ [0,1])
    (d37 : a 37 ∈ [0,1])
    (d39 : a 39 ∈ [0,1,2,3])
    (d42 : a 42 ∈ [0,1])
    (d45 : a 45 ∈ [0])
    (d40 : a 40 ∈ [0,1])
    (d41 : a 41 ∈ [0,2])
    (d44 : a 44 ∈ [0])
    (c71 : edge r71 (a 22) (a 47)=true)
    (c73 : edge r73 (a 23) (a 48)=true)
    (c80 : edge r80 (a 26) (a 51)=true)
    (c82 : edge r82 (a 28) (a 30)=true)
    (c89 : edge r89 (a 32) (a 33)=true)
    (c90 : edge r90 (a 32) (a 35)=true)
    (c92 : edge r92 (a 33) (a 34)=true)
    (c95 : edge r95 (a 34) (a 38)=true)
    (c102 : edge r102 (a 37) (a 38)=true)
    (c106 : edge r106 (a 39) (a 42)=true)
    (c107 : edge r107 (a 39) (a 45)=true)
    (c108 : edge r108 (a 40) (a 41)=true)
    (c110 : edge r110 (a 41) (a 44)=true)
    : a 47 ∈ [0,2] ∧ a 48 ∈ [0] ∧ a 51 ∈ [0] ∧ a 28 ∈ [0] ∧ a 32 ∈ [0] ∧ a 34 ∈ [0] ∧ a 38 ∈ [0] ∧ a 37 ∈ [0] ∧ a 39 ∈ [0] ∧ a 40 ∈ [0] ∧ a 41 ∈ [0] := by
  have b0 : a 47 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 47) (a 22) 1 d22 c71 (by decide +kernel)
  have t0 : a 47 ∈ [0,2,3] := remove (a 47) 1 [0,1,2,3] d47 b0
  have b1 : a 47 ≠ 3 := exclude [0] (fun u v => edge r71 v u) (a 47) (a 22) 3 d22 c71 (by decide +kernel)
  have t1 : a 47 ∈ [0,2] := remove (a 47) 3 [0,2,3] t0 b1
  have b2 : a 48 ≠ 1 := exclude [0] (fun u v => edge r73 v u) (a 48) (a 23) 1 d23 c73 (by decide +kernel)
  have t2 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b2
  have b3 : a 51 ≠ 1 := exclude [0] (fun u v => edge r80 v u) (a 51) (a 26) 1 d26 c80 (by decide +kernel)
  have t3 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b3
  have b4 : a 28 ≠ 2 := exclude [0] (edge r82) (a 28) (a 30) 2 d30 c82 (by decide +kernel)
  have t4 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b4
  have b5 : a 32 ≠ 1 := exclude [0] (edge r89) (a 32) (a 33) 1 d33 c89 (by decide +kernel)
  have t5 : a 32 ∈ [0,2,3] := remove (a 32) 1 [0,1,2,3] d32 b5
  have b6 : a 32 ≠ 3 := exclude [0] (edge r89) (a 32) (a 33) 3 d33 c89 (by decide +kernel)
  have t6 : a 32 ∈ [0,2] := remove (a 32) 3 [0,2,3] t5 b6
  have b7 : a 32 ≠ 2 := exclude [0] (edge r90) (a 32) (a 35) 2 d35 c90 (by decide +kernel)
  have t7 : a 32 ∈ [0] := remove (a 32) 2 [0,2] t6 b7
  have b8 : a 34 ≠ 2 := exclude [0] (fun u v => edge r92 v u) (a 34) (a 33) 2 d33 c92 (by decide +kernel)
  have t8 : a 34 ∈ [0] := remove (a 34) 2 [0,2] d34 b8
  have b9 : a 38 ≠ 1 := exclude [0] (fun u v => edge r95 v u) (a 38) (a 34) 1 t8 c95 (by decide +kernel)
  have t9 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b9
  have b10 : a 37 ≠ 1 := exclude [0] (edge r102) (a 37) (a 38) 1 t9 c102 (by decide +kernel)
  have t10 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b10
  have b11 : a 39 ≠ 2 := exclude [0,1] (edge r106) (a 39) (a 42) 2 d42 c106 (by decide +kernel)
  have t11 : a 39 ∈ [0,1,3] := remove (a 39) 2 [0,1,2,3] d39 b11
  have b12 : a 39 ≠ 3 := exclude [0,1] (edge r106) (a 39) (a 42) 3 d42 c106 (by decide +kernel)
  have t12 : a 39 ∈ [0,1] := remove (a 39) 3 [0,1,3] t11 b12
  have b13 : a 39 ≠ 1 := exclude [0] (edge r107) (a 39) (a 45) 1 d45 c107 (by decide +kernel)
  have t13 : a 39 ∈ [0] := remove (a 39) 1 [0,1] t12 b13
  have b14 : a 40 ≠ 1 := exclude [0,2] (edge r108) (a 40) (a 41) 1 d41 c108 (by decide +kernel)
  have t14 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b14
  have b15 : a 41 ≠ 2 := exclude [0] (edge r110) (a 41) (a 44) 2 d44 c110 (by decide +kernel)
  have t15 : a 41 ∈ [0] := remove (a 41) 2 [0,2] d41 b15
  exact And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t13 (And.intro t14 (t15))))))))))

theorem chunk4 (a : Nat → Nat)
    (d43 : a 43 ∈ [0,2])
    (d44 : a 44 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d47 : a 47 ∈ [0,2])
    (d45 : a 45 ∈ [0])
    (d49 : a 49 ∈ [0,1])
    (d46 : a 46 ∈ [0,2])
    (d48 : a 48 ∈ [0])
    (d52 : a 52 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d5 : a 5 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d8 : a 8 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1])
    (d37 : a 37 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0])
    (d18 : a 18 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (c7 : edge r7 (a 2) (a 5)=true)
    (c19 : edge r19 (a 6) (a 8)=true)
    (c23 : edge r23 (a 7) (a 8)=true)
    (c38 : edge r38 (a 11) (a 37)=true)
    (c44 : edge r44 (a 14) (a 15)=true)
    (c45 : edge r45 (a 14) (a 18)=true)
    (c52 : edge r52 (a 16) (a 18)=true)
    (c54 : edge r54 (a 16) (a 42)=true)
    (c114 : edge r114 (a 43) (a 44)=true)
    (c115 : edge r115 (a 43) (a 50)=true)
    (c118 : edge r118 (a 45) (a 47)=true)
    (c119 : edge r119 (a 45) (a 49)=true)
    (c120 : edge r120 (a 46) (a 48)=true)
    (c124 : edge r124 (a 48) (a 52)=true)
    : a 43 ∈ [0] ∧ a 50 ∈ [0] ∧ a 47 ∈ [0] ∧ a 49 ∈ [0] ∧ a 46 ∈ [0] ∧ a 52 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0,2] ∧ a 11 ∈ [0] ∧ a 14 ∈ [0] ∧ a 16 ∈ [0] ∧ a 42 ∈ [0] := by
  have b0 : a 43 ≠ 2 := exclude [0] (edge r114) (a 43) (a 44) 2 d44 c114 (by decide +kernel)
  have t0 : a 43 ∈ [0] := remove (a 43) 2 [0,2] d43 b0
  have b1 : a 50 ≠ 1 := exclude [0] (fun u v => edge r115 v u) (a 50) (a 43) 1 t0 c115 (by decide +kernel)
  have t1 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b1
  have b2 : a 47 ≠ 2 := exclude [0] (fun u v => edge r118 v u) (a 47) (a 45) 2 d45 c118 (by decide +kernel)
  have t2 : a 47 ∈ [0] := remove (a 47) 2 [0,2] d47 b2
  have b3 : a 49 ≠ 1 := exclude [0] (fun u v => edge r119 v u) (a 49) (a 45) 1 d45 c119 (by decide +kernel)
  have t3 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b3
  have b4 : a 46 ≠ 2 := exclude [0] (edge r120) (a 46) (a 48) 2 d48 c120 (by decide +kernel)
  have t4 : a 46 ∈ [0] := remove (a 46) 2 [0,2] d46 b4
  have b5 : a 52 ≠ 1 := exclude [0] (fun u v => edge r124 v u) (a 52) (a 48) 1 d48 c124 (by decide +kernel)
  have t5 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b5
  have b6 : a 2 ≠ 1 := exclude [0] (edge r7) (a 2) (a 5) 1 d5 c7 (by decide +kernel)
  have t6 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b6
  have b7 : a 6 ≠ 2 := exclude [0] (edge r19) (a 6) (a 8) 2 d8 c19 (by decide +kernel)
  have t7 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b7
  have b8 : a 7 ≠ 1 := exclude [0] (edge r23) (a 7) (a 8) 1 d8 c23 (by decide +kernel)
  have t8 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b8
  have b9 : a 7 ≠ 3 := exclude [0] (edge r23) (a 7) (a 8) 3 d8 c23 (by decide +kernel)
  have t9 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t8 b9
  have b10 : a 11 ≠ 1 := exclude [0] (edge r38) (a 11) (a 37) 1 d37 c38 (by decide +kernel)
  have t10 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b10
  have b11 : a 14 ≠ 1 := exclude [0] (edge r44) (a 14) (a 15) 1 d15 c44 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b11
  have b12 : a 14 ≠ 3 := exclude [0] (edge r44) (a 14) (a 15) 3 d15 c44 (by decide +kernel)
  have t12 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t11 b12
  have b13 : a 14 ≠ 2 := exclude [0] (edge r45) (a 14) (a 18) 2 d18 c45 (by decide +kernel)
  have t13 : a 14 ∈ [0] := remove (a 14) 2 [0,2] t12 b13
  have b14 : a 16 ≠ 1 := exclude [0] (edge r52) (a 16) (a 18) 1 d18 c52 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b14
  have b15 : a 42 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 42) (a 16) 1 t14 c54 (by decide +kernel)
  have t15 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t13 (And.intro t14 (t15))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,2,3])
    (d40 : a 40 ∈ [0])
    (d31 : a 31 ∈ [0,1,2,3])
    (d37 : a 37 ∈ [0])
    (d7 : a 7 ∈ [0,2])
    (d11 : a 11 ∈ [0])
    (c24 : edge r24 (a 7) (a 11)=true)
    (c84 : edge r84 (a 29) (a 31)=true)
    (c85 : edge r85 (a 29) (a 40)=true)
    (c88 : edge r88 (a 31) (a 37)=true)
    : a 29 ∈ [0] ∧ a 31 ∈ [0] ∧ a 7 ∈ [0] := by
  have b0 : a 29 ≠ 1 := exclude [0] (edge r85) (a 29) (a 40) 1 d40 c85 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b0
  have b1 : a 29 ≠ 3 := exclude [0] (edge r85) (a 29) (a 40) 3 d40 c85 (by decide +kernel)
  have t1 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t0 b1
  have b2 : a 31 ≠ 2 := exclude [0] (edge r88) (a 31) (a 37) 2 d37 c88 (by decide +kernel)
  have t2 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b2
  have b3 : a 31 ≠ 3 := exclude [0] (edge r88) (a 31) (a 37) 3 d37 c88 (by decide +kernel)
  have t3 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t2 b3
  have b4 : a 7 ≠ 2 := exclude [0] (edge r24) (a 7) (a 11) 2 d11 c24 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b4
  have b5 : a 29 ≠ 2 := exclude [0,1] (edge r84) (a 29) (a 31) 2 t3 c84 (by decide +kernel)
  have t5 : a 29 ∈ [0] := remove (a 29) 2 [0,2] t1 b5
  have b6 : a 31 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 31) (a 29) 1 t5 c84 (by decide +kernel)
  have t6 : a 31 ∈ [0] := remove (a 31) 1 [0,1] t3 b6
  exact And.intro t5 (And.intro t6 (t4))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1,2,3])
    (start7 : a 7 ∈ [0,1,2,3])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0,1])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1,2,3])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1])
    (start16 : a 16 ∈ [0,1,2,3])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1])
    (start20 : a 20 ∈ [0,1,2,3])
    (start21 : a 21 ∈ [0,1])
    (start22 : a 22 ∈ [0,1])
    (start23 : a 23 ∈ [0,1,2,3])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0,1])
    (start26 : a 26 ∈ [0,1])
    (start27 : a 27 ∈ [0,1])
    (start28 : a 28 ∈ [0,1,2,3])
    (start29 : a 29 ∈ [0,1,2,3])
    (start30 : a 30 ∈ [0,1])
    (start31 : a 31 ∈ [0,1,2,3])
    (start32 : a 32 ∈ [0,1,2,3])
    (start33 : a 33 ∈ [0,1])
    (start34 : a 34 ∈ [0,1,2,3])
    (start35 : a 35 ∈ [0,1])
    (start36 : a 36 ∈ [0,1])
    (start37 : a 37 ∈ [0,1])
    (start38 : a 38 ∈ [0,1])
    (start39 : a 39 ∈ [0,1,2,3])
    (start40 : a 40 ∈ [0,1])
    (start41 : a 41 ∈ [0,1,2,3])
    (start42 : a 42 ∈ [0,1,2,3])
    (start43 : a 43 ∈ [0,1,2,3])
    (start44 : a 44 ∈ [0,1])
    (start45 : a 45 ∈ [0,1])
    (start46 : a 46 ∈ [0,1,2,3])
    (start47 : a 47 ∈ [0,1,2,3])
    (start48 : a 48 ∈ [0,1])
    (start49 : a 49 ∈ [0,1])
    (start50 : a 50 ∈ [0,1])
    (start51 : a 51 ∈ [0,1])
    (start52 : a 52 ∈ [0,1])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 3)=true)
    (c2 : edge r2 (a 1) (a 2)=true)
    (c3 : edge r3 (a 1) (a 4)=true)
    (c4 : edge r4 (a 1) (a 6)=true)
    (c5 : edge r5 (a 1) (a 13)=true)
    (c6 : edge r6 (a 1) (a 28)=true)
    (c7 : edge r7 (a 2) (a 5)=true)
    (c8 : edge r8 (a 2) (a 8)=true)
    (c9 : edge r9 (a 2) (a 15)=true)
    (c10 : edge r10 (a 3) (a 4)=true)
    (c11 : edge r11 (a 3) (a 9)=true)
    (c12 : edge r12 (a 3) (a 16)=true)
    (c13 : edge r13 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 10)=true)
    (c15 : edge r15 (a 4) (a 17)=true)
    (c16 : edge r16 (a 4) (a 30)=true)
    (c17 : edge r17 (a 5) (a 12)=true)
    (c18 : edge r18 (a 5) (a 19)=true)
    (c19 : edge r19 (a 6) (a 8)=true)
    (c20 : edge r20 (a 6) (a 10)=true)
    (c21 : edge r21 (a 6) (a 21)=true)
    (c22 : edge r22 (a 6) (a 33)=true)
    (c23 : edge r23 (a 7) (a 8)=true)
    (c24 : edge r24 (a 7) (a 11)=true)
    (c25 : edge r25 (a 7) (a 22)=true)
    (c26 : edge r26 (a 8) (a 12)=true)
    (c27 : edge r27 (a 8) (a 23)=true)
    (c28 : edge r28 (a 8) (a 34)=true)
    (c29 : edge r29 (a 9) (a 10)=true)
    (c30 : edge r30 (a 9) (a 11)=true)
    (c31 : edge r31 (a 9) (a 24)=true)
    (c32 : edge r32 (a 9) (a 35)=true)
    (c33 : edge r33 (a 10) (a 12)=true)
    (c34 : edge r34 (a 10) (a 25)=true)
    (c35 : edge r35 (a 10) (a 36)=true)
    (c36 : edge r36 (a 11) (a 12)=true)
    (c37 : edge r37 (a 11) (a 26)=true)
    (c38 : edge r38 (a 11) (a 37)=true)
    (c39 : edge r39 (a 12) (a 27)=true)
    (c40 : edge r40 (a 12) (a 38)=true)
    (c41 : edge r41 (a 13) (a 15)=true)
    (c42 : edge r42 (a 13) (a 17)=true)
    (c43 : edge r43 (a 13) (a 21)=true)
    (c44 : edge r44 (a 14) (a 15)=true)
    (c45 : edge r45 (a 14) (a 18)=true)
    (c46 : edge r46 (a 14) (a 22)=true)
    (c47 : edge r47 (a 14) (a 40)=true)
    (c48 : edge r48 (a 15) (a 19)=true)
    (c49 : edge r49 (a 15) (a 23)=true)
    (c50 : edge r50 (a 15) (a 41)=true)
    (c51 : edge r51 (a 16) (a 17)=true)
    (c52 : edge r52 (a 16) (a 18)=true)
    (c53 : edge r53 (a 16) (a 24)=true)
    (c54 : edge r54 (a 16) (a 42)=true)
    (c55 : edge r55 (a 17) (a 19)=true)
    (c56 : edge r56 (a 17) (a 25)=true)
    (c57 : edge r57 (a 17) (a 43)=true)
    (c58 : edge r58 (a 18) (a 19)=true)
    (c59 : edge r59 (a 18) (a 26)=true)
    (c60 : edge r60 (a 19) (a 27)=true)
    (c61 : edge r61 (a 19) (a 44)=true)
    (c62 : edge r62 (a 20) (a 21)=true)
    (c63 : edge r63 (a 20) (a 22)=true)
    (c64 : edge r64 (a 20) (a 24)=true)
    (c65 : edge r65 (a 20) (a 45)=true)
    (c66 : edge r66 (a 21) (a 23)=true)
    (c67 : edge r67 (a 21) (a 25)=true)
    (c68 : edge r68 (a 21) (a 46)=true)
    (c69 : edge r69 (a 22) (a 23)=true)
    (c70 : edge r70 (a 22) (a 26)=true)
    (c71 : edge r71 (a 22) (a 47)=true)
    (c72 : edge r72 (a 23) (a 27)=true)
    (c73 : edge r73 (a 23) (a 48)=true)
    (c74 : edge r74 (a 24) (a 25)=true)
    (c75 : edge r75 (a 24) (a 26)=true)
    (c76 : edge r76 (a 24) (a 49)=true)
    (c77 : edge r77 (a 25) (a 27)=true)
    (c78 : edge r78 (a 25) (a 50)=true)
    (c79 : edge r79 (a 26) (a 27)=true)
    (c80 : edge r80 (a 26) (a 51)=true)
    (c81 : edge r81 (a 27) (a 52)=true)
    (c82 : edge r82 (a 28) (a 30)=true)
    (c83 : edge r83 (a 28) (a 33)=true)
    (c84 : edge r84 (a 29) (a 31)=true)
    (c85 : edge r85 (a 29) (a 40)=true)
    (c86 : edge r86 (a 30) (a 36)=true)
    (c87 : edge r87 (a 30) (a 43)=true)
    (c88 : edge r88 (a 31) (a 37)=true)
    (c89 : edge r89 (a 32) (a 33)=true)
    (c90 : edge r90 (a 32) (a 35)=true)
    (c91 : edge r91 (a 32) (a 45)=true)
    (c92 : edge r92 (a 33) (a 34)=true)
    (c93 : edge r93 (a 33) (a 36)=true)
    (c94 : edge r94 (a 33) (a 46)=true)
    (c95 : edge r95 (a 34) (a 38)=true)
    (c96 : edge r96 (a 34) (a 48)=true)
    (c97 : edge r97 (a 35) (a 36)=true)
    (c98 : edge r98 (a 35) (a 37)=true)
    (c99 : edge r99 (a 35) (a 49)=true)
    (c100 : edge r100 (a 36) (a 38)=true)
    (c101 : edge r101 (a 36) (a 50)=true)
    (c102 : edge r102 (a 37) (a 38)=true)
    (c103 : edge r103 (a 37) (a 51)=true)
    (c104 : edge r104 (a 38) (a 52)=true)
    (c105 : edge r105 (a 39) (a 40)=true)
    (c106 : edge r106 (a 39) (a 42)=true)
    (c107 : edge r107 (a 39) (a 45)=true)
    (c108 : edge r108 (a 40) (a 41)=true)
    (c109 : edge r109 (a 40) (a 47)=true)
    (c110 : edge r110 (a 41) (a 44)=true)
    (c111 : edge r111 (a 41) (a 48)=true)
    (c112 : edge r112 (a 42) (a 43)=true)
    (c113 : edge r113 (a 42) (a 49)=true)
    (c114 : edge r114 (a 43) (a 44)=true)
    (c115 : edge r115 (a 43) (a 50)=true)
    (c116 : edge r116 (a 44) (a 52)=true)
    (c117 : edge r117 (a 45) (a 46)=true)
    (c118 : edge r118 (a 45) (a 47)=true)
    (c119 : edge r119 (a 45) (a 49)=true)
    (c120 : edge r120 (a 46) (a 48)=true)
    (c121 : edge r121 (a 46) (a 50)=true)
    (c122 : edge r122 (a 47) (a 48)=true)
    (c123 : edge r123 (a 47) (a 51)=true)
    (c124 : edge r124 (a 48) (a 52)=true)
    (c125 : edge r125 (a 49) (a 50)=true)
    (c126 : edge r126 (a 49) (a 51)=true)
    (c127 : edge r127 (a 50) (a 52)=true)
    (c128 : edge r128 (a 51) (a 52)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0 ∧ a 32=0 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=0 ∧ a 37=0 ∧ a 38=0 ∧ a 39=0 ∧ a 40=0 ∧ a 41=0 ∧ a 42=0 ∧ a 43=0 ∧ a 44=0 ∧ a 45=0 ∧ a 46=0 ∧ a 47=0 ∧ a 48=0 ∧ a 49=0 ∧ a 50=0 ∧ a 51=0 ∧ a 52=0) := by
  have group1 := chunk0 a start3 start0 start6 start1 start13 start28 start4 start9 start16 start5 start17 start30 start12 start19 c1 c4 c5 c6 c10 c11 c12 c13 c15 c16 c17 c18
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
  have group14 := chunk1 a start10 h3 start21 start33 start8 h12 start23 start34 start24 h7 start35 start25 start36 h4 h10 start15 start41 c20 c21 c22 c26 c27 c28 c31 c32 c34 c35 c42 c49 c50
  rcases group14 with ⟨h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27⟩
  have group28 := chunk2 a start42 h8 start43 h10 start18 h13 start27 start44 start20 h16 h21 start45 h19 start46 start22 start26 c54 c57 c58 c60 c61 c62 c64 c65 c66 c68 c69 c70
  rcases group28 with ⟨h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39⟩
  have group40 := chunk3 a start47 h38 start48 h36 start51 h39 h5 h11 start32 h17 h22 h20 start38 start37 start39 h29 h35 start40 h27 h33 c71 c73 c80 c82 c89 c90 c92 c95 c102 c106 c107 c108 c110
  rcases group40 with ⟨h41,h42,h43,h44,h45,h46,h47,h48,h49,h50,h51⟩
  have group52 := chunk4 a h30 h33 start50 h41 h35 start49 h37 h42 start52 start2 h9 h3 h18 start7 start11 h48 start14 h26 h31 h8 h29 c7 c19 c23 c38 c44 c45 c52 c54 c114 c115 c118 c119 c120 c124
  rcases group52 with ⟨h53,h54,h55,h56,h57,h58,h59,h60,h61,h62,h63,h64,h65⟩
  have group66 := chunk5 a start29 h50 start31 h48 h61 h62 c24 c84 c85 c88
  rcases group66 with ⟨h67,h68,h69⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h59) (And.intro (forced (a 3) 0 h2) (And.intro (forced (a 4) 0 h6) (And.intro (forced (a 5) 0 h9) (And.intro (forced (a 6) 0 h60) (And.intro (forced (a 7) 0 h69) (And.intro (forced (a 8) 0 h18) (And.intro (forced (a 9) 0 h7) (And.intro (forced (a 10) 0 h15) (And.intro (forced (a 11) 0 h62) (And.intro (forced (a 12) 0 h12) (And.intro (forced (a 13) 0 h25) (And.intro (forced (a 14) 0 h63) (And.intro (forced (a 15) 0 h26) (And.intro (forced (a 16) 0 h64) (And.intro (forced (a 17) 0 h10) (And.intro (forced (a 18) 0 h31) (And.intro (forced (a 19) 0 h13) (And.intro (forced (a 20) 0 h34) (And.intro (forced (a 21) 0 h16) (And.intro (forced (a 22) 0 h38) (And.intro (forced (a 23) 0 h36) (And.intro (forced (a 24) 0 h21) (And.intro (forced (a 25) 0 h23) (And.intro (forced (a 26) 0 h39) (And.intro (forced (a 27) 0 h32) (And.intro (forced (a 28) 0 h44) (And.intro (forced (a 29) 0 h67) (And.intro (forced (a 30) 0 h11) (And.intro (forced (a 31) 0 h68) (And.intro (forced (a 32) 0 h45) (And.intro (forced (a 33) 0 h17) (And.intro (forced (a 34) 0 h46) (And.intro (forced (a 35) 0 h22) (And.intro (forced (a 36) 0 h24) (And.intro (forced (a 37) 0 h48) (And.intro (forced (a 38) 0 h47) (And.intro (forced (a 39) 0 h49) (And.intro (forced (a 40) 0 h50) (And.intro (forced (a 41) 0 h51) (And.intro (forced (a 42) 0 h65) (And.intro (forced (a 43) 0 h53) (And.intro (forced (a 44) 0 h33) (And.intro (forced (a 45) 0 h35) (And.intro (forced (a 46) 0 h57) (And.intro (forced (a 47) 0 h55) (And.intro (forced (a 48) 0 h42) (And.intro (forced (a 49) 0 h56) (And.intro (forced (a 50) 0 h54) (And.intro (forced (a 51) 0 h43) (forced (a 52) 0 h58))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_245
