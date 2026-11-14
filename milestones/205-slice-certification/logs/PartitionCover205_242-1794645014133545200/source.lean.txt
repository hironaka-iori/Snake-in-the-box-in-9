import FiniteDomain205
namespace PartitionCover205_242
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[1]
def r5 : Array Nat := #[1]
def r6 : Array Nat := #[1]
def r7 : Array Nat := #[1,1]
def r8 : Array Nat := #[1,2]
def r9 : Array Nat := #[3,12]
def r10 : Array Nat := #[3,12]
def r11 : Array Nat := #[3,12]
def r12 : Array Nat := #[1]
def r13 : Array Nat := #[3]
def r14 : Array Nat := #[3]
def r15 : Array Nat := #[5]
def r16 : Array Nat := #[1,1]
def r17 : Array Nat := #[3]
def r18 : Array Nat := #[3]
def r19 : Array Nat := #[1,1]
def r20 : Array Nat := #[3,12]
def r21 : Array Nat := #[5,10]
def r22 : Array Nat := #[3,12]
def r23 : Array Nat := #[1,2]
def r24 : Array Nat := #[3]
def r25 : Array Nat := #[3]
def r26 : Array Nat := #[3]
def r27 : Array Nat := #[3]
def r28 : Array Nat := #[1,1,2,2]
def r29 : Array Nat := #[1,2,1,2]
def r30 : Array Nat := #[1,2]
def r31 : Array Nat := #[3,12]
def r32 : Array Nat := #[3,12]
def r33 : Array Nat := #[1,2,4,8]
def r34 : Array Nat := #[1,1,2,2]
def r35 : Array Nat := #[1,2,0,0]
def r36 : Array Nat := #[1,4,2,8]
def r37 : Array Nat := #[1,2,1,2]
def r38 : Array Nat := #[1,1]
def r39 : Array Nat := #[1,1]
def r40 : Array Nat := #[1]
def r41 : Array Nat := #[5]
def r42 : Array Nat := #[3]
def r43 : Array Nat := #[5]
def r44 : Array Nat := #[5]
def r45 : Array Nat := #[3]
def r46 : Array Nat := #[3]
def r47 : Array Nat := #[3]
def r48 : Array Nat := #[3]
def r49 : Array Nat := #[1,1,2,2]
def r50 : Array Nat := #[1,2,1,2]
def r51 : Array Nat := #[1,2,1,2]
def r52 : Array Nat := #[1,2]
def r53 : Array Nat := #[3,12]
def r54 : Array Nat := #[3,3]
def r55 : Array Nat := #[1,2]
def r56 : Array Nat := #[1,2]
def r57 : Array Nat := #[1,4]
def r58 : Array Nat := #[1,2]
def r59 : Array Nat := #[3,3]
def r60 : Array Nat := #[3,12]
def r61 : Array Nat := #[1,1,2,2]
def r62 : Array Nat := #[1,2,1,2]
def r63 : Array Nat := #[3,12]
def r64 : Array Nat := #[3,12]
def r65 : Array Nat := #[3,12]
def r66 : Array Nat := #[5,10]
def r67 : Array Nat := #[3,12]
def r68 : Array Nat := #[5,10]
def r69 : Array Nat := #[1,2,1,2]
def r70 : Array Nat := #[1,1,2,2]
def r71 : Array Nat := #[1,2,1,2]
def r72 : Array Nat := #[1,2,1,2]
def r73 : Array Nat := #[1,1,2,2]
def r74 : Array Nat := #[1,2,1,2]
def r75 : Array Nat := #[3,12]
def r76 : Array Nat := #[1,2,4,8]
def r77 : Array Nat := #[1,2,1,2]
def r78 : Array Nat := #[1,2,4,8]
def r79 : Array Nat := #[1,2,1,2]
def r80 : Array Nat := #[1,1,2,2]
def r81 : Array Nat := #[1,2,1,2]
def r82 : Array Nat := #[1,2]
def r83 : Array Nat := #[1,2]
def r84 : Array Nat := #[1,2]
def r85 : Array Nat := #[1,1]
def r86 : Array Nat := #[1,4]
def r87 : Array Nat := #[1,2]
def r88 : Array Nat := #[1,4]
def r89 : Array Nat := #[1,2,1,2]
def r90 : Array Nat := #[1,1,2,2]
def r91 : Array Nat := #[3,3]
def r92 : Array Nat := #[3,12]
def r93 : Array Nat := #[3,12]
def r94 : Array Nat := #[3,3]
def r95 : Array Nat := #[3,3]
def r96 : Array Nat := #[1,1,2,2]
def r97 : Array Nat := #[1,2,1,2]
def r98 : Array Nat := #[3,12]
def r99 : Array Nat := #[1,1,2,2]
def r100 : Array Nat := #[1,2,1,2]
def r101 : Array Nat := #[3,3]
def r102 : Array Nat := #[1,2]
def r103 : Array Nat := #[3,12]
def r104 : Array Nat := #[1,2]
def r105 : Array Nat := #[5,10]
def r106 : Array Nat := #[5,10]
def r107 : Array Nat := #[5,10]
def r108 : Array Nat := #[3,3]
def r109 : Array Nat := #[3,12]
def r110 : Array Nat := #[3,3]
def r111 : Array Nat := #[1,2,4,8]
def r112 : Array Nat := #[1,1,2,2]
def r113 : Array Nat := #[1,4,2,8]
def r114 : Array Nat := #[1,1,2,2]
def r115 : Array Nat := #[1,2,1,2]
def r116 : Array Nat := #[1,1,2,2]
def r117 : Array Nat := #[1,1,2,2]
def r118 : Array Nat := #[5,10]
def r119 : Array Nat := #[1,1,2,2]
def r120 : Array Nat := #[1,2,1,2]
def r121 : Array Nat := #[3,12]
def r122 : Array Nat := #[5,10]
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d0 : a 0 ∈ [0])
    (d6 : a 6 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d8 : a 8 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1,2,3])
    (d27 : a 27 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d10 : a 10 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 6)=true)
    (c8 : edge r8 (a 2) (a 4)=true)
    (c9 : edge r9 (a 2) (a 8)=true)
    (c10 : edge r10 (a 2) (a 15)=true)
    (c11 : edge r11 (a 2) (a 27)=true)
    (c15 : edge r15 (a 3) (a 28)=true)
    (c21 : edge r21 (a 6) (a 10)=true)
    (c22 : edge r22 (a 6) (a 20)=true)
    (c23 : edge r23 (a 6) (a 31)=true)
    : a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 4 ∈ [0] ∧ a 8 ∈ [0,1] ∧ a 15 ∈ [0,1] ∧ a 27 ∈ [0,1] ∧ a 28 ∈ [0,2] ∧ a 10 ∈ [0,2] ∧ a 20 ∈ [0,1] ∧ a 31 ∈ [0] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 6 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 6) (a 0) 1 d0 c2 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b1
  have b2 : a 4 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 4) (a 2) 1 t0 c8 (by decide +kernel)
  have t2 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b2
  have b3 : a 8 ≠ 2 := exclude [0] (fun u v => edge r9 v u) (a 8) (a 2) 2 t0 c9 (by decide +kernel)
  have t3 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b3
  have b4 : a 8 ≠ 3 := exclude [0] (fun u v => edge r9 v u) (a 8) (a 2) 3 t0 c9 (by decide +kernel)
  have t4 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t3 b4
  have b5 : a 15 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 15) (a 2) 2 t0 c10 (by decide +kernel)
  have t5 : a 15 ∈ [0,1,3] := remove (a 15) 2 [0,1,2,3] d15 b5
  have b6 : a 15 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 15) (a 2) 3 t0 c10 (by decide +kernel)
  have t6 : a 15 ∈ [0,1] := remove (a 15) 3 [0,1,3] t5 b6
  have b7 : a 27 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 27) (a 2) 2 t0 c11 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,3] := remove (a 27) 2 [0,1,2,3] d27 b7
  have b8 : a 27 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 27) (a 2) 3 t0 c11 (by decide +kernel)
  have t8 : a 27 ∈ [0,1] := remove (a 27) 3 [0,1,3] t7 b8
  have b9 : a 28 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 28) (a 3) 1 d3 c15 (by decide +kernel)
  have t9 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b9
  have b10 : a 28 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 28) (a 3) 3 d3 c15 (by decide +kernel)
  have t10 : a 28 ∈ [0,2] := remove (a 28) 3 [0,2,3] t9 b10
  have b11 : a 10 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 6) 1 t1 c21 (by decide +kernel)
  have t11 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b11
  have b12 : a 10 ≠ 3 := exclude [0] (fun u v => edge r21 v u) (a 10) (a 6) 3 t1 c21 (by decide +kernel)
  have t12 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t11 b12
  have b13 : a 20 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 20) (a 6) 2 t1 c22 (by decide +kernel)
  have t13 : a 20 ∈ [0,1,3] := remove (a 20) 2 [0,1,2,3] d20 b13
  have b14 : a 20 ≠ 3 := exclude [0] (fun u v => edge r22 v u) (a 20) (a 6) 3 t1 c22 (by decide +kernel)
  have t14 : a 20 ∈ [0,1] := remove (a 20) 3 [0,1,3] t13 b14
  have b15 : a 31 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 31) (a 6) 1 t1 c23 (by decide +kernel)
  have t15 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15)))))))))

theorem chunk1 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3])
    (d33 : a 33 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,2])
    (d34 : a 34 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (c25 : edge r25 (a 7) (a 11)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 9) (a 12)=true)
    (c31 : edge r31 (a 9) (a 23)=true)
    (c32 : edge r32 (a 9) (a 33)=true)
    (c33 : edge r33 (a 10) (a 11)=true)
    (c34 : edge r34 (a 10) (a 34)=true)
    (c36 : edge r36 (a 11) (a 24)=true)
    (c37 : edge r37 (a 11) (a 35)=true)
    (c38 : edge r38 (a 12) (a 26)=true)
    : a 11 ∈ [0] ∧ a 9 ∈ [0] ∧ a 12 ∈ [0] ∧ a 23 ∈ [0,1] ∧ a 33 ∈ [0,1] ∧ a 10 ∈ [0] ∧ a 34 ∈ [0] ∧ a 24 ∈ [0] ∧ a 35 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 11 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 11) (a 7) 2 d7 c25 (by decide +kernel)
  have t0 : a 11 ∈ [0,1,3] := remove (a 11) 2 [0,1,2,3] d11 b0
  have b1 : a 11 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 11) (a 7) 3 d7 c25 (by decide +kernel)
  have t1 : a 11 ∈ [0,1] := remove (a 11) 3 [0,1,3] t0 b1
  have b2 : a 9 ≠ 1 := exclude [0,1] (fun u v => edge r28 v u) (a 9) (a 8) 1 d8 c28 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b2
  have b3 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 9) 1 t2 c30 (by decide +kernel)
  have t3 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b3
  have b4 : a 23 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 23) (a 9) 2 t2 c31 (by decide +kernel)
  have t4 : a 23 ∈ [0,1,3] := remove (a 23) 2 [0,1,2,3] d23 b4
  have b5 : a 23 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 23) (a 9) 3 t2 c31 (by decide +kernel)
  have t5 : a 23 ∈ [0,1] := remove (a 23) 3 [0,1,3] t4 b5
  have b6 : a 33 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 33) (a 9) 2 t2 c32 (by decide +kernel)
  have t6 : a 33 ∈ [0,1,3] := remove (a 33) 2 [0,1,2,3] d33 b6
  have b7 : a 33 ≠ 3 := exclude [0] (fun u v => edge r32 v u) (a 33) (a 9) 3 t2 c32 (by decide +kernel)
  have t7 : a 33 ∈ [0,1] := remove (a 33) 3 [0,1,3] t6 b7
  have b8 : a 10 ≠ 2 := exclude [0,1] (edge r33) (a 10) (a 11) 2 t1 c33 (by decide +kernel)
  have t8 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b8
  have b9 : a 11 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 11) (a 10) 1 t8 c33 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 1 [0,1] t1 b9
  have b10 : a 34 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 34) (a 10) 1 t8 c34 (by decide +kernel)
  have t10 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b10
  have b11 : a 24 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 24) (a 11) 1 t9 c36 (by decide +kernel)
  have t11 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b11
  have b12 : a 24 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 24) (a 11) 2 t9 c36 (by decide +kernel)
  have t12 : a 24 ∈ [0,3] := remove (a 24) 2 [0,2,3] t11 b12
  have b13 : a 24 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 24) (a 11) 3 t9 c36 (by decide +kernel)
  have t13 : a 24 ∈ [0] := remove (a 24) 3 [0,3] t12 b13
  have b14 : a 35 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 35) (a 11) 1 t9 c37 (by decide +kernel)
  have t14 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b14
  have b15 : a 26 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 26) (a 12) 1 t3 c38 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b15
  exact And.intro t9 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t13 (And.intro t14 (t15)))))))))

theorem chunk2 (a : Nat → Nat)
    (d37 : a 37 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d38 : a 38 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d44 : a 44 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,1])
    (d45 : a 45 ∈ [0,1,2,3])
    (c39 : edge r39 (a 12) (a 37)=true)
    (c41 : edge r41 (a 13) (a 15)=true)
    (c43 : edge r43 (a 13) (a 20)=true)
    (c44 : edge r44 (a 13) (a 38)=true)
    (c49 : edge r49 (a 15) (a 16)=true)
    (c50 : edge r50 (a 15) (a 22)=true)
    (c51 : edge r51 (a 15) (a 40)=true)
    (c52 : edge r52 (a 16) (a 19)=true)
    (c56 : edge r56 (a 18) (a 19)=true)
    (c58 : edge r58 (a 18) (a 42)=true)
    (c60 : edge r60 (a 19) (a 44)=true)
    (c61 : edge r61 (a 20) (a 21)=true)
    (c65 : edge r65 (a 21) (a 45)=true)
    : a 37 ∈ [0] ∧ a 15 ∈ [0] ∧ a 20 ∈ [0] ∧ a 38 ∈ [0,2] ∧ a 16 ∈ [0] ∧ a 22 ∈ [0] ∧ a 40 ∈ [0] ∧ a 19 ∈ [0] ∧ a 18 ∈ [0] ∧ a 42 ∈ [0] ∧ a 44 ∈ [0,1] ∧ a 21 ∈ [0] ∧ a 45 ∈ [0,1] := by
  have b0 : a 37 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 37) (a 12) 1 d12 c39 (by decide +kernel)
  have t0 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b0
  have b1 : a 15 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 15) (a 13) 1 d13 c41 (by decide +kernel)
  have t1 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b1
  have b2 : a 20 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 20) (a 13) 1 d13 c43 (by decide +kernel)
  have t2 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b2
  have b3 : a 38 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 38) (a 13) 1 d13 c44 (by decide +kernel)
  have t3 : a 38 ∈ [0,2,3] := remove (a 38) 1 [0,1,2,3] d38 b3
  have b4 : a 38 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 38) (a 13) 3 d13 c44 (by decide +kernel)
  have t4 : a 38 ∈ [0,2] := remove (a 38) 3 [0,2,3] t3 b4
  have b5 : a 16 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 16) (a 15) 1 t1 c49 (by decide +kernel)
  have t5 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b5
  have b6 : a 22 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 22) (a 15) 1 t1 c50 (by decide +kernel)
  have t6 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b6
  have b7 : a 40 ≠ 1 := exclude [0] (fun u v => edge r51 v u) (a 40) (a 15) 1 t1 c51 (by decide +kernel)
  have t7 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b7
  have b8 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 16) 1 t5 c52 (by decide +kernel)
  have t8 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b8
  have b9 : a 18 ≠ 1 := exclude [0] (edge r56) (a 18) (a 19) 1 t8 c56 (by decide +kernel)
  have t9 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b9
  have b10 : a 42 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 42) (a 18) 1 t9 c58 (by decide +kernel)
  have t10 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b10
  have b11 : a 44 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 44) (a 19) 2 t8 c60 (by decide +kernel)
  have t11 : a 44 ∈ [0,1,3] := remove (a 44) 2 [0,1,2,3] d44 b11
  have b12 : a 44 ≠ 3 := exclude [0] (fun u v => edge r60 v u) (a 44) (a 19) 3 t8 c60 (by decide +kernel)
  have t12 : a 44 ∈ [0,1] := remove (a 44) 3 [0,1,3] t11 b12
  have b13 : a 21 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 21) (a 20) 1 t2 c61 (by decide +kernel)
  have t13 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b13
  have b14 : a 45 ≠ 2 := exclude [0] (fun u v => edge r65 v u) (a 45) (a 21) 2 t13 c65 (by decide +kernel)
  have t14 : a 45 ∈ [0,1,3] := remove (a 45) 2 [0,1,2,3] d45 b14
  have b15 : a 45 ≠ 3 := exclude [0] (fun u v => edge r65 v u) (a 45) (a 21) 3 t13 c65 (by decide +kernel)
  have t15 : a 45 ∈ [0,1] := remove (a 45) 3 [0,1,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))))))))))

theorem chunk3 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3])
    (d46 : a 46 ∈ [0,1,2,3])
    (d47 : a 47 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d51 : a 51 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0])
    (d27 : a 27 ∈ [0,1])
    (d28 : a 28 ∈ [0,2])
    (d33 : a 33 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (c66 : edge r66 (a 22) (a 23)=true)
    (c67 : edge r67 (a 22) (a 25)=true)
    (c68 : edge r68 (a 22) (a 46)=true)
    (c70 : edge r70 (a 23) (a 47)=true)
    (c72 : edge r72 (a 24) (a 49)=true)
    (c75 : edge r75 (a 26) (a 51)=true)
    (c76 : edge r76 (a 27) (a 28)=true)
    (c78 : edge r78 (a 28) (a 33)=true)
    (c79 : edge r79 (a 28) (a 41)=true)
    (c81 : edge r81 (a 29) (a 34)=true)
    (c82 : edge r82 (a 30) (a 35)=true)
    : a 23 ∈ [0] ∧ a 25 ∈ [0,1] ∧ a 46 ∈ [0,2] ∧ a 47 ∈ [0] ∧ a 49 ∈ [0] ∧ a 51 ∈ [0,1] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 33 ∈ [0] ∧ a 41 ∈ [0] ∧ a 29 ∈ [0,2] ∧ a 30 ∈ [0] := by
  have b0 : a 23 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 23) (a 22) 1 d22 c66 (by decide +kernel)
  have t0 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b0
  have b1 : a 25 ≠ 2 := exclude [0] (fun u v => edge r67 v u) (a 25) (a 22) 2 d22 c67 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,3] := remove (a 25) 2 [0,1,2,3] d25 b1
  have b2 : a 25 ≠ 3 := exclude [0] (fun u v => edge r67 v u) (a 25) (a 22) 3 d22 c67 (by decide +kernel)
  have t2 : a 25 ∈ [0,1] := remove (a 25) 3 [0,1,3] t1 b2
  have b3 : a 46 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 46) (a 22) 1 d22 c68 (by decide +kernel)
  have t3 : a 46 ∈ [0,2,3] := remove (a 46) 1 [0,1,2,3] d46 b3
  have b4 : a 46 ≠ 3 := exclude [0] (fun u v => edge r68 v u) (a 46) (a 22) 3 d22 c68 (by decide +kernel)
  have t4 : a 46 ∈ [0,2] := remove (a 46) 3 [0,2,3] t3 b4
  have b5 : a 47 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 47) (a 23) 1 t0 c70 (by decide +kernel)
  have t5 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b5
  have b6 : a 49 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 49) (a 24) 1 d24 c72 (by decide +kernel)
  have t6 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b6
  have b7 : a 51 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 51) (a 26) 2 d26 c75 (by decide +kernel)
  have t7 : a 51 ∈ [0,1,3] := remove (a 51) 2 [0,1,2,3] d51 b7
  have b8 : a 51 ≠ 3 := exclude [0] (fun u v => edge r75 v u) (a 51) (a 26) 3 d26 c75 (by decide +kernel)
  have t8 : a 51 ∈ [0,1] := remove (a 51) 3 [0,1,3] t7 b8
  have b9 : a 27 ≠ 1 := exclude [0,2] (edge r76) (a 27) (a 28) 1 d28 c76 (by decide +kernel)
  have t9 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b9
  have b10 : a 28 ≠ 2 := exclude [0] (fun u v => edge r76 v u) (a 28) (a 27) 2 t9 c76 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b10
  have b11 : a 33 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 33) (a 28) 1 t10 c78 (by decide +kernel)
  have t11 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b11
  have b12 : a 41 ≠ 1 := exclude [0] (fun u v => edge r79 v u) (a 41) (a 28) 1 t10 c79 (by decide +kernel)
  have t12 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b12
  have b13 : a 29 ≠ 1 := exclude [0] (edge r81) (a 29) (a 34) 1 d34 c81 (by decide +kernel)
  have t13 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b13
  have b14 : a 29 ≠ 3 := exclude [0] (edge r81) (a 29) (a 34) 3 d34 c81 (by decide +kernel)
  have t14 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t13 b14
  have b15 : a 30 ≠ 1 := exclude [0] (edge r82) (a 30) (a 35) 1 d35 c82 (by decide +kernel)
  have t15 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t14 (t15)))))))))))

theorem chunk4 (a : Nat → Nat)
    (d32 : a 32 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d45 : a 45 ∈ [0,1])
    (d36 : a 36 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0])
    (d48 : a 48 ∈ [0,1,2,3])
    (d39 : a 39 ∈ [0,1])
    (d42 : a 42 ∈ [0])
    (d43 : a 43 ∈ [0,1,2,3])
    (d40 : a 40 ∈ [0])
    (d44 : a 44 ∈ [0,1])
    (d41 : a 41 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d46 : a 46 ∈ [0,2])
    (d47 : a 47 ∈ [0])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (c29 : edge r29 (a 8) (a 22)=true)
    (c84 : edge r84 (a 31) (a 32)=true)
    (c88 : edge r88 (a 32) (a 45)=true)
    (c92 : edge r92 (a 34) (a 36)=true)
    (c93 : edge r93 (a 34) (a 48)=true)
    (c102 : edge r102 (a 39) (a 42)=true)
    (c105 : edge r105 (a 40) (a 43)=true)
    (c107 : edge r107 (a 41) (a 44)=true)
    (c111 : edge r111 (a 43) (a 44)=true)
    (c112 : edge r112 (a 43) (a 50)=true)
    (c113 : edge r113 (a 44) (a 51)=true)
    (c116 : edge r116 (a 46) (a 47)=true)
    (c120 : edge r120 (a 48) (a 50)=true)
    : a 32 ∈ [0] ∧ a 45 ∈ [0] ∧ a 36 ∈ [0,1] ∧ a 48 ∈ [0] ∧ a 39 ∈ [0] ∧ a 43 ∈ [0] ∧ a 44 ∈ [0] ∧ a 50 ∈ [0] ∧ a 51 ∈ [0] ∧ a 46 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 32 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 32) (a 31) 1 d31 c84 (by decide +kernel)
  have t0 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b0
  have b1 : a 45 ≠ 1 := exclude [0] (fun u v => edge r88 v u) (a 45) (a 32) 1 t0 c88 (by decide +kernel)
  have t1 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b1
  have b2 : a 36 ≠ 2 := exclude [0] (fun u v => edge r92 v u) (a 36) (a 34) 2 d34 c92 (by decide +kernel)
  have t2 : a 36 ∈ [0,1,3] := remove (a 36) 2 [0,1,2,3] d36 b2
  have b3 : a 36 ≠ 3 := exclude [0] (fun u v => edge r92 v u) (a 36) (a 34) 3 d34 c92 (by decide +kernel)
  have t3 : a 36 ∈ [0,1] := remove (a 36) 3 [0,1,3] t2 b3
  have b4 : a 48 ≠ 2 := exclude [0] (fun u v => edge r93 v u) (a 48) (a 34) 2 d34 c93 (by decide +kernel)
  have t4 : a 48 ∈ [0,1,3] := remove (a 48) 2 [0,1,2,3] d48 b4
  have b5 : a 48 ≠ 3 := exclude [0] (fun u v => edge r93 v u) (a 48) (a 34) 3 d34 c93 (by decide +kernel)
  have t5 : a 48 ∈ [0,1] := remove (a 48) 3 [0,1,3] t4 b5
  have b6 : a 39 ≠ 1 := exclude [0] (edge r102) (a 39) (a 42) 1 d42 c102 (by decide +kernel)
  have t6 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b6
  have b7 : a 43 ≠ 1 := exclude [0] (fun u v => edge r105 v u) (a 43) (a 40) 1 d40 c105 (by decide +kernel)
  have t7 : a 43 ∈ [0,2,3] := remove (a 43) 1 [0,1,2,3] d43 b7
  have b8 : a 43 ≠ 3 := exclude [0] (fun u v => edge r105 v u) (a 43) (a 40) 3 d40 c105 (by decide +kernel)
  have t8 : a 43 ∈ [0,2] := remove (a 43) 3 [0,2,3] t7 b8
  have b9 : a 44 ≠ 1 := exclude [0] (fun u v => edge r107 v u) (a 44) (a 41) 1 d41 c107 (by decide +kernel)
  have t9 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b9
  have b10 : a 43 ≠ 2 := exclude [0] (edge r111) (a 43) (a 44) 2 t9 c111 (by decide +kernel)
  have t10 : a 43 ∈ [0] := remove (a 43) 2 [0,2] t8 b10
  have b11 : a 50 ≠ 1 := exclude [0] (fun u v => edge r112 v u) (a 50) (a 43) 1 t10 c112 (by decide +kernel)
  have t11 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b11
  have b12 : a 51 ≠ 1 := exclude [0] (fun u v => edge r113 v u) (a 51) (a 44) 1 t9 c113 (by decide +kernel)
  have t12 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b12
  have b13 : a 46 ≠ 2 := exclude [0] (edge r116) (a 46) (a 47) 2 d47 c116 (by decide +kernel)
  have t13 : a 46 ∈ [0] := remove (a 46) 2 [0,2] d46 b13
  have b14 : a 48 ≠ 1 := exclude [0] (edge r120) (a 48) (a 50) 1 t11 c120 (by decide +kernel)
  have t14 : a 48 ∈ [0] := remove (a 48) 1 [0,1] t5 b14
  have b15 : a 8 ≠ 1 := exclude [0] (edge r29) (a 8) (a 22) 1 d22 c29 (by decide +kernel)
  have t15 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t14 (And.intro t6 (And.intro t10 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t13 (t15))))))))))

theorem chunk5 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d50 : a 50 ∈ [0])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d36 : a 36 ∈ [0,1])
    (d38 : a 38 ∈ [0,2])
    (d39 : a 39 ∈ [0])
    (c55 : edge r55 (a 17) (a 18)=true)
    (c74 : edge r74 (a 25) (a 50)=true)
    (c80 : edge r80 (a 29) (a 30)=true)
    (c97 : edge r97 (a 36) (a 50)=true)
    (c99 : edge r99 (a 38) (a 39)=true)
    : a 17 ∈ [0] ∧ a 25 ∈ [0] ∧ a 29 ∈ [0] ∧ a 36 ∈ [0] ∧ a 38 ∈ [0] := by
  have b0 : a 17 ≠ 1 := exclude [0] (edge r55) (a 17) (a 18) 1 d18 c55 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b0
  have b1 : a 25 ≠ 1 := exclude [0] (edge r74) (a 25) (a 50) 1 d50 c74 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b1
  have b2 : a 29 ≠ 2 := exclude [0] (edge r80) (a 29) (a 30) 2 d30 c80 (by decide +kernel)
  have t2 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b2
  have b3 : a 36 ≠ 1 := exclude [0] (edge r97) (a 36) (a 50) 1 d50 c97 (by decide +kernel)
  have t3 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b3
  have b4 : a 38 ≠ 2 := exclude [0] (edge r99) (a 38) (a 39) 2 d39 c99 (by decide +kernel)
  have t4 : a 38 ∈ [0] := remove (a 38) 2 [0,2] d38 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0])
    (start8 : a 8 ∈ [0,1,2,3])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0,1,2,3])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0])
    (start14 : a 14 ∈ [0])
    (start15 : a 15 ∈ [0,1,2,3])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1])
    (start20 : a 20 ∈ [0,1,2,3])
    (start21 : a 21 ∈ [0,1])
    (start22 : a 22 ∈ [0,1])
    (start23 : a 23 ∈ [0,1,2,3])
    (start24 : a 24 ∈ [0,1,2,3])
    (start25 : a 25 ∈ [0,1,2,3])
    (start26 : a 26 ∈ [0,1])
    (start27 : a 27 ∈ [0,1,2,3])
    (start28 : a 28 ∈ [0,1,2,3])
    (start29 : a 29 ∈ [0,1,2,3])
    (start30 : a 30 ∈ [0,1])
    (start31 : a 31 ∈ [0,1])
    (start32 : a 32 ∈ [0,1])
    (start33 : a 33 ∈ [0,1,2,3])
    (start34 : a 34 ∈ [0,1])
    (start35 : a 35 ∈ [0,1])
    (start36 : a 36 ∈ [0,1,2,3])
    (start37 : a 37 ∈ [0,1])
    (start38 : a 38 ∈ [0,1,2,3])
    (start39 : a 39 ∈ [0,1])
    (start40 : a 40 ∈ [0,1])
    (start41 : a 41 ∈ [0,1])
    (start42 : a 42 ∈ [0,1])
    (start43 : a 43 ∈ [0,1,2,3])
    (start44 : a 44 ∈ [0,1,2,3])
    (start45 : a 45 ∈ [0,1,2,3])
    (start46 : a 46 ∈ [0,1,2,3])
    (start47 : a 47 ∈ [0,1])
    (start48 : a 48 ∈ [0,1,2,3])
    (start49 : a 49 ∈ [0,1])
    (start50 : a 50 ∈ [0,1])
    (start51 : a 51 ∈ [0,1,2,3])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 6)=true)
    (c3 : edge r3 (a 0) (a 13)=true)
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 7)=true)
    (c6 : edge r6 (a 1) (a 14)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 4)=true)
    (c9 : edge r9 (a 2) (a 8)=true)
    (c10 : edge r10 (a 2) (a 15)=true)
    (c11 : edge r11 (a 2) (a 27)=true)
    (c12 : edge r12 (a 3) (a 5)=true)
    (c13 : edge r13 (a 3) (a 9)=true)
    (c14 : edge r14 (a 3) (a 16)=true)
    (c15 : edge r15 (a 3) (a 28)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 5) (a 12)=true)
    (c18 : edge r18 (a 5) (a 19)=true)
    (c19 : edge r19 (a 6) (a 7)=true)
    (c20 : edge r20 (a 6) (a 8)=true)
    (c21 : edge r21 (a 6) (a 10)=true)
    (c22 : edge r22 (a 6) (a 20)=true)
    (c23 : edge r23 (a 6) (a 31)=true)
    (c24 : edge r24 (a 7) (a 9)=true)
    (c25 : edge r25 (a 7) (a 11)=true)
    (c26 : edge r26 (a 7) (a 21)=true)
    (c27 : edge r27 (a 7) (a 32)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 22)=true)
    (c30 : edge r30 (a 9) (a 12)=true)
    (c31 : edge r31 (a 9) (a 23)=true)
    (c32 : edge r32 (a 9) (a 33)=true)
    (c33 : edge r33 (a 10) (a 11)=true)
    (c34 : edge r34 (a 10) (a 34)=true)
    (c35 : edge r35 (a 11) (a 12)=true)
    (c36 : edge r36 (a 11) (a 24)=true)
    (c37 : edge r37 (a 11) (a 35)=true)
    (c38 : edge r38 (a 12) (a 26)=true)
    (c39 : edge r39 (a 12) (a 37)=true)
    (c40 : edge r40 (a 13) (a 14)=true)
    (c41 : edge r41 (a 13) (a 15)=true)
    (c42 : edge r42 (a 13) (a 17)=true)
    (c43 : edge r43 (a 13) (a 20)=true)
    (c44 : edge r44 (a 13) (a 38)=true)
    (c45 : edge r45 (a 14) (a 16)=true)
    (c46 : edge r46 (a 14) (a 18)=true)
    (c47 : edge r47 (a 14) (a 21)=true)
    (c48 : edge r48 (a 14) (a 39)=true)
    (c49 : edge r49 (a 15) (a 16)=true)
    (c50 : edge r50 (a 15) (a 22)=true)
    (c51 : edge r51 (a 15) (a 40)=true)
    (c52 : edge r52 (a 16) (a 19)=true)
    (c53 : edge r53 (a 16) (a 23)=true)
    (c54 : edge r54 (a 16) (a 41)=true)
    (c55 : edge r55 (a 17) (a 18)=true)
    (c56 : edge r56 (a 18) (a 19)=true)
    (c57 : edge r57 (a 18) (a 24)=true)
    (c58 : edge r58 (a 18) (a 42)=true)
    (c59 : edge r59 (a 19) (a 26)=true)
    (c60 : edge r60 (a 19) (a 44)=true)
    (c61 : edge r61 (a 20) (a 21)=true)
    (c62 : edge r62 (a 20) (a 22)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 24)=true)
    (c65 : edge r65 (a 21) (a 45)=true)
    (c66 : edge r66 (a 22) (a 23)=true)
    (c67 : edge r67 (a 22) (a 25)=true)
    (c68 : edge r68 (a 22) (a 46)=true)
    (c69 : edge r69 (a 23) (a 26)=true)
    (c70 : edge r70 (a 23) (a 47)=true)
    (c71 : edge r71 (a 24) (a 26)=true)
    (c72 : edge r72 (a 24) (a 49)=true)
    (c73 : edge r73 (a 25) (a 26)=true)
    (c74 : edge r74 (a 25) (a 50)=true)
    (c75 : edge r75 (a 26) (a 51)=true)
    (c76 : edge r76 (a 27) (a 28)=true)
    (c77 : edge r77 (a 27) (a 40)=true)
    (c78 : edge r78 (a 28) (a 33)=true)
    (c79 : edge r79 (a 28) (a 41)=true)
    (c80 : edge r80 (a 29) (a 30)=true)
    (c81 : edge r81 (a 29) (a 34)=true)
    (c82 : edge r82 (a 30) (a 35)=true)
    (c83 : edge r83 (a 30) (a 42)=true)
    (c84 : edge r84 (a 31) (a 32)=true)
    (c85 : edge r85 (a 31) (a 34)=true)
    (c86 : edge r86 (a 32) (a 33)=true)
    (c87 : edge r87 (a 32) (a 35)=true)
    (c88 : edge r88 (a 32) (a 45)=true)
    (c89 : edge r89 (a 33) (a 37)=true)
    (c90 : edge r90 (a 33) (a 47)=true)
    (c91 : edge r91 (a 34) (a 35)=true)
    (c92 : edge r92 (a 34) (a 36)=true)
    (c93 : edge r93 (a 34) (a 48)=true)
    (c94 : edge r94 (a 35) (a 37)=true)
    (c95 : edge r95 (a 35) (a 49)=true)
    (c96 : edge r96 (a 36) (a 37)=true)
    (c97 : edge r97 (a 36) (a 50)=true)
    (c98 : edge r98 (a 37) (a 51)=true)
    (c99 : edge r99 (a 38) (a 39)=true)
    (c100 : edge r100 (a 38) (a 40)=true)
    (c101 : edge r101 (a 39) (a 41)=true)
    (c102 : edge r102 (a 39) (a 42)=true)
    (c103 : edge r103 (a 39) (a 45)=true)
    (c104 : edge r104 (a 40) (a 41)=true)
    (c105 : edge r105 (a 40) (a 43)=true)
    (c106 : edge r106 (a 40) (a 46)=true)
    (c107 : edge r107 (a 41) (a 44)=true)
    (c108 : edge r108 (a 41) (a 47)=true)
    (c109 : edge r109 (a 42) (a 44)=true)
    (c110 : edge r110 (a 42) (a 49)=true)
    (c111 : edge r111 (a 43) (a 44)=true)
    (c112 : edge r112 (a 43) (a 50)=true)
    (c113 : edge r113 (a 44) (a 51)=true)
    (c114 : edge r114 (a 45) (a 47)=true)
    (c115 : edge r115 (a 45) (a 49)=true)
    (c116 : edge r116 (a 46) (a 47)=true)
    (c117 : edge r117 (a 46) (a 50)=true)
    (c118 : edge r118 (a 47) (a 51)=true)
    (c119 : edge r119 (a 48) (a 49)=true)
    (c120 : edge r120 (a 48) (a 50)=true)
    (c121 : edge r121 (a 49) (a 51)=true)
    (c122 : edge r122 (a 50) (a 51)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0 ∧ a 32=0 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=0 ∧ a 37=0 ∧ a 38=0 ∧ a 39=0 ∧ a 40=0 ∧ a 41=0 ∧ a 42=0 ∧ a 43=0 ∧ a 44=0 ∧ a 45=0 ∧ a 46=0 ∧ a 47=0 ∧ a 48=0 ∧ a 49=0 ∧ a 50=0 ∧ a 51=0) := by
  have group1 := chunk0 a start2 start0 start6 start4 start8 start15 start27 start28 start3 start10 start20 start31 c1 c2 c8 c9 c10 c11 c15 c21 c22 c23
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
  have group12 := chunk1 a start11 start7 start9 h5 start12 start23 start33 h9 start34 start24 start35 start26 c25 c28 c30 c31 c32 c33 c34 c36 c37 c38
  rcases group12 with ⟨h13,h14,h15,h16,h17,h18,h19,h20,h21,h22⟩
  have group23 := chunk2 a start37 h15 h6 start13 h10 start38 start16 start22 start40 start19 start18 start42 start44 start21 start45 c39 c41 c43 c44 c49 c50 c51 c52 c56 c58 c60 c61 c65
  rcases group23 with ⟨h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36⟩
  have group37 := chunk3 a h16 h29 start25 start46 start47 start49 h20 start51 h22 h7 h8 h17 start41 start29 h19 start30 h21 c66 c67 c68 c70 c72 c75 c76 c78 c79 c81 c82
  rcases group37 with ⟨h38,h39,h40,h41,h42,h43,h44,h45,h46,h47,h48,h49⟩
  have group50 := chunk4 a start32 h11 h36 start36 h19 start48 start39 h33 start43 h30 h34 h47 start50 h43 h40 h41 h5 h29 c29 c84 c88 c92 c93 c102 c105 c107 c111 c112 c113 c116 c120
  rcases group50 with ⟨h51,h52,h53,h54,h55,h56,h57,h58,h59,h60,h61⟩
  have group62 := chunk5 a start17 h32 h39 h58 h48 h49 h53 h27 h55 c55 c74 c80 c97 c99
  rcases group62 with ⟨h63,h64,h65,h66,h67⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h4) (And.intro (forced (a 5) 0 start5) (And.intro (forced (a 6) 0 h3) (And.intro (forced (a 7) 0 start7) (And.intro (forced (a 8) 0 h61) (And.intro (forced (a 9) 0 h14) (And.intro (forced (a 10) 0 h18) (And.intro (forced (a 11) 0 h13) (And.intro (forced (a 12) 0 h15) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 0 start14) (And.intro (forced (a 15) 0 h25) (And.intro (forced (a 16) 0 h28) (And.intro (forced (a 17) 0 h63) (And.intro (forced (a 18) 0 h32) (And.intro (forced (a 19) 0 h31) (And.intro (forced (a 20) 0 h26) (And.intro (forced (a 21) 0 h35) (And.intro (forced (a 22) 0 h29) (And.intro (forced (a 23) 0 h38) (And.intro (forced (a 24) 0 h20) (And.intro (forced (a 25) 0 h64) (And.intro (forced (a 26) 0 h22) (And.intro (forced (a 27) 0 h44) (And.intro (forced (a 28) 0 h45) (And.intro (forced (a 29) 0 h65) (And.intro (forced (a 30) 0 h49) (And.intro (forced (a 31) 0 h11) (And.intro (forced (a 32) 0 h51) (And.intro (forced (a 33) 0 h46) (And.intro (forced (a 34) 0 h19) (And.intro (forced (a 35) 0 h21) (And.intro (forced (a 36) 0 h66) (And.intro (forced (a 37) 0 h24) (And.intro (forced (a 38) 0 h67) (And.intro (forced (a 39) 0 h55) (And.intro (forced (a 40) 0 h30) (And.intro (forced (a 41) 0 h47) (And.intro (forced (a 42) 0 h33) (And.intro (forced (a 43) 0 h56) (And.intro (forced (a 44) 0 h57) (And.intro (forced (a 45) 0 h52) (And.intro (forced (a 46) 0 h60) (And.intro (forced (a 47) 0 h41) (And.intro (forced (a 48) 0 h54) (And.intro (forced (a 49) 0 h42) (And.intro (forced (a 50) 0 h58) (forced (a 51) 0 h59)))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_242
