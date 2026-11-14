import FiniteDomain205
namespace PartitionCover205_218
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[3]
def r4 : Array Nat := #[3]
def r5 : Array Nat := #[3]
def r6 : Array Nat := #[1]
def r7 : Array Nat := #[3]
def r8 : Array Nat := #[3]
def r9 : Array Nat := #[1]
def r10 : Array Nat := #[3]
def r11 : Array Nat := #[1]
def r12 : Array Nat := #[3]
def r13 : Array Nat := #[3]
def r14 : Array Nat := #[5]
def r15 : Array Nat := #[3]
def r16 : Array Nat := #[1]
def r17 : Array Nat := #[3]
def r18 : Array Nat := #[1]
def r19 : Array Nat := #[1]
def r20 : Array Nat := #[1,2]
def r21 : Array Nat := #[1,2]
def r22 : Array Nat := #[1,1]
def r23 : Array Nat := #[1,1]
def r24 : Array Nat := #[1,1]
def r25 : Array Nat := #[1,1]
def r26 : Array Nat := #[1,1]
def r27 : Array Nat := #[3,12]
def r28 : Array Nat := #[1,1]
def r29 : Array Nat := #[1,1]
def r30 : Array Nat := #[1,2]
def r31 : Array Nat := #[1,2]
def r32 : Array Nat := #[1,1]
def r33 : Array Nat := #[1]
def r34 : Array Nat := #[3]
def r35 : Array Nat := #[1,2]
def r36 : Array Nat := #[1,2]
def r37 : Array Nat := #[1,1]
def r38 : Array Nat := #[1,2]
def r39 : Array Nat := #[1,1]
def r40 : Array Nat := #[1,2]
def r41 : Array Nat := #[1,1]
def r42 : Array Nat := #[1,2]
def r43 : Array Nat := #[1,1]
def r44 : Array Nat := #[1,2]
def r45 : Array Nat := #[1,2]
def r46 : Array Nat := #[1,2]
def r47 : Array Nat := #[1,1]
def r48 : Array Nat := #[1,2]
def r49 : Array Nat := #[1,1]
def r50 : Array Nat := #[1]
def r51 : Array Nat := #[3]
def r52 : Array Nat := #[1]
def r53 : Array Nat := #[3]
def r54 : Array Nat := #[1]
def r55 : Array Nat := #[3]
def r56 : Array Nat := #[1,1]
def r57 : Array Nat := #[1,1]
def r58 : Array Nat := #[1,1]
def r59 : Array Nat := #[3]
def r60 : Array Nat := #[3]
def r61 : Array Nat := #[1,1]
def r62 : Array Nat := #[3,12]
def r63 : Array Nat := #[1,1]
def r64 : Array Nat := #[1,2]
def r65 : Array Nat := #[1]
def r66 : Array Nat := #[5]
def r67 : Array Nat := #[3]
def r68 : Array Nat := #[5]
def r69 : Array Nat := #[1,0,1,0]
def r70 : Array Nat := #[1,0,2,0]
def r71 : Array Nat := #[1,2,4,8]
def r72 : Array Nat := #[3]
def r73 : Array Nat := #[1]
def r74 : Array Nat := #[5]
def r75 : Array Nat := #[3]
def r76 : Array Nat := #[1]
def r77 : Array Nat := #[3]
def r78 : Array Nat := #[1,0,1,0]
def r79 : Array Nat := #[1,1]
def r80 : Array Nat := #[1,2]
def r81 : Array Nat := #[1,1]
def r82 : Array Nat := #[1,2]
def r83 : Array Nat := #[1,2]
def r84 : Array Nat := #[1,1]
def r85 : Array Nat := #[1,2]
def r86 : Array Nat := #[1,2]
def r87 : Array Nat := #[1]
def r88 : Array Nat := #[3]
def r89 : Array Nat := #[3]
def r90 : Array Nat := #[1]
def r91 : Array Nat := #[1,2]
def r92 : Array Nat := #[1,2]
def r93 : Array Nat := #[1,1]
def r94 : Array Nat := #[1,1]
def r95 : Array Nat := #[1,1]
def r96 : Array Nat := #[1,1]
def r97 : Array Nat := #[1,1]
def r98 : Array Nat := #[3,12]
def r99 : Array Nat := #[1,1]
def r100 : Array Nat := #[1,1]
def r101 : Array Nat := #[1,2]
def r102 : Array Nat := #[3,12]
def r103 : Array Nat := #[3]
def r104 : Array Nat := #[1]
def r105 : Array Nat := #[1]
def r106 : Array Nat := #[1]
def r107 : Array Nat := #[1]
def r108 : Array Nat := #[3]
def r109 : Array Nat := #[3]
def r110 : Array Nat := #[3]
def r111 : Array Nat := #[3]
def r112 : Array Nat := #[1]
def r113 : Array Nat := #[3]
def r114 : Array Nat := #[1]
def r115 : Array Nat := #[1,2]
def r116 : Array Nat := #[3,12]
def r117 : Array Nat := #[1]
def r118 : Array Nat := #[3]
def r119 : Array Nat := #[3]
def r120 : Array Nat := #[3]
def r121 : Array Nat := #[1]
def r122 : Array Nat := #[3]
def r123 : Array Nat := #[1]
def r124 : Array Nat := #[1,1]
def r125 : Array Nat := #[1,1]
def r126 : Array Nat := #[1,2]
def r127 : Array Nat := #[3]
def r128 : Array Nat := #[3]
def r129 : Array Nat := #[1,2]
def r130 : Array Nat := #[1,1]
def r131 : Array Nat := #[1,2]
def r132 : Array Nat := #[1,2]
def r133 : Array Nat := #[1,1]
def r134 : Array Nat := #[3]
def r135 : Array Nat := #[1]
def r136 : Array Nat := #[1,0,1,0]
def r137 : Array Nat := #[1,0,1,0]
def r138 : Array Nat := #[1,0,1,0]
def r139 : Array Nat := #[1,0,1,0]
def r140 : Array Nat := #[1,0,2,0]
def r141 : Array Nat := #[5]
def r142 : Array Nat := #[3]
def r143 : Array Nat := #[1,1]
def r144 : Array Nat := #[1,2]
def r145 : Array Nat := #[5]
def r146 : Array Nat := #[1]
def r147 : Array Nat := #[1,1]
def r148 : Array Nat := #[1,2]
def r149 : Array Nat := #[1,2]
def r150 : Array Nat := #[3]
def r151 : Array Nat := #[1]
def r152 : Array Nat := #[1,2]
def r153 : Array Nat := #[1,1]
def r154 : Array Nat := #[1,1]
def r155 : Array Nat := #[1,1]
theorem chunk0 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0])
    (d45 : a 45 ∈ [0,1,2,3])
    (d46 : a 46 ∈ [0,1,2,3])
    (d50 : a 50 ∈ [0,1,2,3])
    (d47 : a 47 ∈ [0])
    (c14 : edge r14 (a 2) (a 18)=true)
    (c66 : edge r66 (a 17) (a 21)=true)
    (c68 : edge r68 (a 17) (a 45)=true)
    (c71 : edge r71 (a 18) (a 46)=true)
    (c141 : edge r141 (a 47) (a 50)=true)
    : a 18 ∈ [0,2] ∧ a 21 ∈ [0,2] ∧ a 45 ∈ [0,2] ∧ a 46 ∈ [0,2] ∧ a 50 ∈ [0,2] := by
  have b0 : a 18 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 18) (a 2) 1 d2 c14 (by decide +kernel)
  have t0 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b0
  have b1 : a 18 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 18) (a 2) 3 d2 c14 (by decide +kernel)
  have t1 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] t0 b1
  have b2 : a 21 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 21) (a 17) 1 d17 c66 (by decide +kernel)
  have t2 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b2
  have b3 : a 21 ≠ 3 := exclude [0] (fun u v => edge r66 v u) (a 21) (a 17) 3 d17 c66 (by decide +kernel)
  have t3 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] t2 b3
  have b4 : a 45 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 45) (a 17) 1 d17 c68 (by decide +kernel)
  have t4 : a 45 ∈ [0,2,3] := remove (a 45) 1 [0,1,2,3] d45 b4
  have b5 : a 45 ≠ 3 := exclude [0] (fun u v => edge r68 v u) (a 45) (a 17) 3 d17 c68 (by decide +kernel)
  have t5 : a 45 ∈ [0,2] := remove (a 45) 3 [0,2,3] t4 b5
  have b6 : a 46 ≠ 1 := exclude [0,2] (fun u v => edge r71 v u) (a 46) (a 18) 1 t1 c71 (by decide +kernel)
  have t6 : a 46 ∈ [0,2,3] := remove (a 46) 1 [0,1,2,3] d46 b6
  have b7 : a 46 ≠ 3 := exclude [0,2] (fun u v => edge r71 v u) (a 46) (a 18) 3 t1 c71 (by decide +kernel)
  have t7 : a 46 ∈ [0,2] := remove (a 46) 3 [0,2,3] t6 b7
  have b8 : a 50 ≠ 1 := exclude [0] (fun u v => edge r141 v u) (a 50) (a 47) 1 d47 c141 (by decide +kernel)
  have t8 : a 50 ∈ [0,2,3] := remove (a 50) 1 [0,1,2,3] d50 b8
  have b9 : a 50 ≠ 3 := exclude [0] (fun u v => edge r141 v u) (a 50) (a 47) 3 d47 c141 (by decide +kernel)
  have t9 : a 50 ∈ [0,2] := remove (a 50) 3 [0,2,3] t8 b9
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (t9))))

theorem chunk1 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d6 : a 6 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d39 : a 39 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d46 : a 46 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d54 : a 54 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (c20 : edge r20 (a 4) (a 5)=true)
    (c21 : edge r21 (a 4) (a 6)=true)
    (c27 : edge r27 (a 5) (a 21)=true)
    (c30 : edge r30 (a 6) (a 14)=true)
    (c31 : edge r31 (a 6) (a 22)=true)
    (c36 : edge r36 (a 8) (a 10)=true)
    (c38 : edge r38 (a 8) (a 23)=true)
    (c45 : edge r45 (a 10) (a 14)=true)
    (c46 : edge r46 (a 10) (a 39)=true)
    (c70 : edge r70 (a 18) (a 22)=true)
    (c71 : edge r71 (a 18) (a 46)=true)
    (c101 : edge r101 (a 31) (a 39)=true)
    (c126 : edge r126 (a 39) (a 53)=true)
    (c148 : edge r148 (a 51) (a 53)=true)
    (c149 : edge r149 (a 51) (a 55)=true)
    (c152 : edge r152 (a 53) (a 54)=true)
    : a 5 ∈ [0] ∧ a 6 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 10 ∈ [0] ∧ a 39 ∈ [0] ∧ a 18 ∈ [0] ∧ a 46 ∈ [0] ∧ a 31 ∈ [0] ∧ a 53 ∈ [0] ∧ a 51 ∈ [0] ∧ a 55 ∈ [0] ∧ a 54 ∈ [0] ∧ a 8 ∈ [0] ∧ a 23 ∈ [0] := by
  have b0 : a 5 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 5) (a 4) 1 d4 c20 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b0
  have b1 : a 6 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 6) (a 4) 1 d4 c21 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b1
  have b2 : a 21 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 21) (a 5) 2 t0 c27 (by decide +kernel)
  have t2 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b2
  have b3 : a 14 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 14) (a 6) 1 t1 c30 (by decide +kernel)
  have t3 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b3
  have b4 : a 22 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 22) (a 6) 1 t1 c31 (by decide +kernel)
  have t4 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b4
  have b5 : a 10 ≠ 1 := exclude [0] (edge r45) (a 10) (a 14) 1 t3 c45 (by decide +kernel)
  have t5 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b5
  have b6 : a 39 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 39) (a 10) 1 t5 c46 (by decide +kernel)
  have t6 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b6
  have b7 : a 18 ≠ 2 := exclude [0] (edge r70) (a 18) (a 22) 2 t4 c70 (by decide +kernel)
  have t7 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b7
  have b8 : a 46 ≠ 2 := exclude [0] (fun u v => edge r71 v u) (a 46) (a 18) 2 t7 c71 (by decide +kernel)
  have t8 : a 46 ∈ [0] := remove (a 46) 2 [0,2] d46 b8
  have b9 : a 31 ≠ 1 := exclude [0] (edge r101) (a 31) (a 39) 1 t6 c101 (by decide +kernel)
  have t9 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b9
  have b10 : a 53 ≠ 1 := exclude [0] (fun u v => edge r126 v u) (a 53) (a 39) 1 t6 c126 (by decide +kernel)
  have t10 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b10
  have b11 : a 51 ≠ 1 := exclude [0] (edge r148) (a 51) (a 53) 1 t10 c148 (by decide +kernel)
  have t11 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b11
  have b12 : a 55 ≠ 1 := exclude [0] (fun u v => edge r149 v u) (a 55) (a 51) 1 t11 c149 (by decide +kernel)
  have t12 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b12
  have b13 : a 54 ≠ 1 := exclude [0] (fun u v => edge r152 v u) (a 54) (a 53) 1 t10 c152 (by decide +kernel)
  have t13 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b13
  have b14 : a 8 ≠ 1 := exclude [0] (edge r36) (a 8) (a 10) 1 t5 c36 (by decide +kernel)
  have t14 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b14
  have b15 : a 23 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 23) (a 8) 1 t14 c38 (by decide +kernel)
  have t15 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk2 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d41 : a 41 ∈ [0,1])
    (d55 : a 55 ∈ [0])
    (d48 : a 48 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d45 : a 45 ∈ [0,2])
    (d42 : a 42 ∈ [0,1])
    (d44 : a 44 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d50 : a 50 ∈ [0,2])
    (c35 : edge r35 (a 8) (a 9)=true)
    (c44 : edge r44 (a 10) (a 11)=true)
    (c48 : edge r48 (a 11) (a 25)=true)
    (c62 : edge r62 (a 16) (a 18)=true)
    (c80 : edge r80 (a 23) (a 24)=true)
    (c85 : edge r85 (a 25) (a 28)=true)
    (c91 : edge r91 (a 29) (a 30)=true)
    (c92 : edge r92 (a 29) (a 31)=true)
    (c98 : edge r98 (a 30) (a 45)=true)
    (c115 : edge r115 (a 36) (a 44)=true)
    (c116 : edge r116 (a 36) (a 50)=true)
    (c129 : edge r129 (a 41) (a 42)=true)
    (c131 : edge r131 (a 41) (a 55)=true)
    (c132 : edge r132 (a 42) (a 44)=true)
    (c144 : edge r144 (a 48) (a 55)=true)
    : a 11 ∈ [0] ∧ a 25 ∈ [0] ∧ a 16 ∈ [0] ∧ a 24 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 41 ∈ [0] ∧ a 48 ∈ [0] ∧ a 9 ∈ [0] ∧ a 30 ∈ [0] ∧ a 45 ∈ [0] ∧ a 42 ∈ [0] ∧ a 44 ∈ [0] ∧ a 36 ∈ [0] ∧ a 50 ∈ [0] := by
  have b0 : a 11 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 11) (a 10) 1 d10 c44 (by decide +kernel)
  have t0 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b0
  have b1 : a 25 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 25) (a 11) 1 t0 c48 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b1
  have b2 : a 16 ≠ 1 := exclude [0] (edge r62) (a 16) (a 18) 1 d18 c62 (by decide +kernel)
  have t2 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b2
  have b3 : a 24 ≠ 1 := exclude [0] (fun u v => edge r80 v u) (a 24) (a 23) 1 d23 c80 (by decide +kernel)
  have t3 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b3
  have b4 : a 28 ≠ 1 := exclude [0] (fun u v => edge r85 v u) (a 28) (a 25) 1 t1 c85 (by decide +kernel)
  have t4 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b4
  have b5 : a 29 ≠ 1 := exclude [0] (edge r92) (a 29) (a 31) 1 d31 c92 (by decide +kernel)
  have t5 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b5
  have b6 : a 41 ≠ 1 := exclude [0] (edge r131) (a 41) (a 55) 1 d55 c131 (by decide +kernel)
  have t6 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b6
  have b7 : a 48 ≠ 1 := exclude [0] (edge r144) (a 48) (a 55) 1 d55 c144 (by decide +kernel)
  have t7 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b7
  have b8 : a 9 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 9) (a 8) 1 d8 c35 (by decide +kernel)
  have t8 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b8
  have b9 : a 30 ≠ 1 := exclude [0] (fun u v => edge r91 v u) (a 30) (a 29) 1 t5 c91 (by decide +kernel)
  have t9 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b9
  have b10 : a 45 ≠ 2 := exclude [0] (fun u v => edge r98 v u) (a 45) (a 30) 2 t9 c98 (by decide +kernel)
  have t10 : a 45 ∈ [0] := remove (a 45) 2 [0,2] d45 b10
  have b11 : a 42 ≠ 1 := exclude [0] (fun u v => edge r129 v u) (a 42) (a 41) 1 t6 c129 (by decide +kernel)
  have t11 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b11
  have b12 : a 44 ≠ 1 := exclude [0] (fun u v => edge r132 v u) (a 44) (a 42) 1 t11 c132 (by decide +kernel)
  have t12 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b12
  have b13 : a 36 ≠ 1 := exclude [0] (edge r115) (a 36) (a 44) 1 t12 c115 (by decide +kernel)
  have t13 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b13
  have b14 : a 50 ≠ 2 := exclude [0] (fun u v => edge r116 v u) (a 50) (a 36) 2 t13 c116 (by decide +kernel)
  have t14 : a 50 ∈ [0] := remove (a 50) 2 [0,2] d50 b14
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (t14))))))))))))))

theorem chunk3 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [1])
    (d6 : a 6 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d39 : a 39 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d46 : a 46 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d54 : a 54 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (c20 : edge r20 (a 4) (a 5)=true)
    (c21 : edge r21 (a 4) (a 6)=true)
    (c27 : edge r27 (a 5) (a 21)=true)
    (c30 : edge r30 (a 6) (a 14)=true)
    (c31 : edge r31 (a 6) (a 22)=true)
    (c36 : edge r36 (a 8) (a 10)=true)
    (c38 : edge r38 (a 8) (a 23)=true)
    (c45 : edge r45 (a 10) (a 14)=true)
    (c46 : edge r46 (a 10) (a 39)=true)
    (c70 : edge r70 (a 18) (a 22)=true)
    (c71 : edge r71 (a 18) (a 46)=true)
    (c101 : edge r101 (a 31) (a 39)=true)
    (c126 : edge r126 (a 39) (a 53)=true)
    (c148 : edge r148 (a 51) (a 53)=true)
    (c149 : edge r149 (a 51) (a 55)=true)
    (c152 : edge r152 (a 53) (a 54)=true)
    : a 5 ∈ [1] ∧ a 6 ∈ [1] ∧ a 21 ∈ [2] ∧ a 14 ∈ [1] ∧ a 22 ∈ [1] ∧ a 10 ∈ [1] ∧ a 39 ∈ [1] ∧ a 18 ∈ [2] ∧ a 46 ∈ [2] ∧ a 31 ∈ [1] ∧ a 53 ∈ [1] ∧ a 51 ∈ [1] ∧ a 55 ∈ [1] ∧ a 54 ∈ [1] ∧ a 8 ∈ [1] ∧ a 23 ∈ [1] := by
  have b0 : a 5 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 5) (a 4) 0 d4 c20 (by decide +kernel)
  have t0 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b0
  have b1 : a 6 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 6) (a 4) 0 d4 c21 (by decide +kernel)
  have t1 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b1
  have b2 : a 21 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 21) (a 5) 0 t0 c27 (by decide +kernel)
  have t2 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b2
  have b3 : a 14 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 14) (a 6) 0 t1 c30 (by decide +kernel)
  have t3 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b3
  have b4 : a 22 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 22) (a 6) 0 t1 c31 (by decide +kernel)
  have t4 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b4
  have b5 : a 10 ≠ 0 := exclude [1] (edge r45) (a 10) (a 14) 0 t3 c45 (by decide +kernel)
  have t5 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b5
  have b6 : a 39 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 39) (a 10) 0 t5 c46 (by decide +kernel)
  have t6 : a 39 ∈ [1] := remove (a 39) 0 [0,1] d39 b6
  have b7 : a 18 ≠ 0 := exclude [1] (edge r70) (a 18) (a 22) 0 t4 c70 (by decide +kernel)
  have t7 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b7
  have b8 : a 46 ≠ 0 := exclude [2] (fun u v => edge r71 v u) (a 46) (a 18) 0 t7 c71 (by decide +kernel)
  have t8 : a 46 ∈ [2] := remove (a 46) 0 [0,2] d46 b8
  have b9 : a 31 ≠ 0 := exclude [1] (edge r101) (a 31) (a 39) 0 t6 c101 (by decide +kernel)
  have t9 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b9
  have b10 : a 53 ≠ 0 := exclude [1] (fun u v => edge r126 v u) (a 53) (a 39) 0 t6 c126 (by decide +kernel)
  have t10 : a 53 ∈ [1] := remove (a 53) 0 [0,1] d53 b10
  have b11 : a 51 ≠ 0 := exclude [1] (edge r148) (a 51) (a 53) 0 t10 c148 (by decide +kernel)
  have t11 : a 51 ∈ [1] := remove (a 51) 0 [0,1] d51 b11
  have b12 : a 55 ≠ 0 := exclude [1] (fun u v => edge r149 v u) (a 55) (a 51) 0 t11 c149 (by decide +kernel)
  have t12 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b12
  have b13 : a 54 ≠ 0 := exclude [1] (fun u v => edge r152 v u) (a 54) (a 53) 0 t10 c152 (by decide +kernel)
  have t13 : a 54 ∈ [1] := remove (a 54) 0 [0,1] d54 b13
  have b14 : a 8 ≠ 0 := exclude [1] (edge r36) (a 8) (a 10) 0 t5 c36 (by decide +kernel)
  have t14 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b14
  have b15 : a 23 ≠ 0 := exclude [1] (fun u v => edge r38 v u) (a 23) (a 8) 0 t14 c38 (by decide +kernel)
  have t15 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk4 (a : Nat → Nat)
    (d11 : a 11 ∈ [0,1])
    (d10 : a 10 ∈ [1])
    (d25 : a 25 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [2])
    (d24 : a 24 ∈ [0,1])
    (d23 : a 23 ∈ [1])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [1])
    (d41 : a 41 ∈ [0,1])
    (d55 : a 55 ∈ [1])
    (d48 : a 48 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d45 : a 45 ∈ [0,2])
    (d42 : a 42 ∈ [0,1])
    (d44 : a 44 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d50 : a 50 ∈ [0,2])
    (c35 : edge r35 (a 8) (a 9)=true)
    (c44 : edge r44 (a 10) (a 11)=true)
    (c48 : edge r48 (a 11) (a 25)=true)
    (c62 : edge r62 (a 16) (a 18)=true)
    (c80 : edge r80 (a 23) (a 24)=true)
    (c85 : edge r85 (a 25) (a 28)=true)
    (c91 : edge r91 (a 29) (a 30)=true)
    (c92 : edge r92 (a 29) (a 31)=true)
    (c98 : edge r98 (a 30) (a 45)=true)
    (c115 : edge r115 (a 36) (a 44)=true)
    (c116 : edge r116 (a 36) (a 50)=true)
    (c129 : edge r129 (a 41) (a 42)=true)
    (c131 : edge r131 (a 41) (a 55)=true)
    (c132 : edge r132 (a 42) (a 44)=true)
    (c144 : edge r144 (a 48) (a 55)=true)
    : a 11 ∈ [1] ∧ a 25 ∈ [1] ∧ a 16 ∈ [1] ∧ a 24 ∈ [1] ∧ a 28 ∈ [1] ∧ a 29 ∈ [1] ∧ a 41 ∈ [1] ∧ a 48 ∈ [1] ∧ a 9 ∈ [1] ∧ a 30 ∈ [1] ∧ a 45 ∈ [2] ∧ a 42 ∈ [1] ∧ a 44 ∈ [1] ∧ a 36 ∈ [1] ∧ a 50 ∈ [2] := by
  have b0 : a 11 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 11) (a 10) 0 d10 c44 (by decide +kernel)
  have t0 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b0
  have b1 : a 25 ≠ 0 := exclude [1] (fun u v => edge r48 v u) (a 25) (a 11) 0 t0 c48 (by decide +kernel)
  have t1 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b1
  have b2 : a 16 ≠ 0 := exclude [2] (edge r62) (a 16) (a 18) 0 d18 c62 (by decide +kernel)
  have t2 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b2
  have b3 : a 24 ≠ 0 := exclude [1] (fun u v => edge r80 v u) (a 24) (a 23) 0 d23 c80 (by decide +kernel)
  have t3 : a 24 ∈ [1] := remove (a 24) 0 [0,1] d24 b3
  have b4 : a 28 ≠ 0 := exclude [1] (fun u v => edge r85 v u) (a 28) (a 25) 0 t1 c85 (by decide +kernel)
  have t4 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b4
  have b5 : a 29 ≠ 0 := exclude [1] (edge r92) (a 29) (a 31) 0 d31 c92 (by decide +kernel)
  have t5 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b5
  have b6 : a 41 ≠ 0 := exclude [1] (edge r131) (a 41) (a 55) 0 d55 c131 (by decide +kernel)
  have t6 : a 41 ∈ [1] := remove (a 41) 0 [0,1] d41 b6
  have b7 : a 48 ≠ 0 := exclude [1] (edge r144) (a 48) (a 55) 0 d55 c144 (by decide +kernel)
  have t7 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b7
  have b8 : a 9 ≠ 0 := exclude [1] (fun u v => edge r35 v u) (a 9) (a 8) 0 d8 c35 (by decide +kernel)
  have t8 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b8
  have b9 : a 30 ≠ 0 := exclude [1] (fun u v => edge r91 v u) (a 30) (a 29) 0 t5 c91 (by decide +kernel)
  have t9 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b9
  have b10 : a 45 ≠ 0 := exclude [1] (fun u v => edge r98 v u) (a 45) (a 30) 0 t9 c98 (by decide +kernel)
  have t10 : a 45 ∈ [2] := remove (a 45) 0 [0,2] d45 b10
  have b11 : a 42 ≠ 0 := exclude [1] (fun u v => edge r129 v u) (a 42) (a 41) 0 t6 c129 (by decide +kernel)
  have t11 : a 42 ∈ [1] := remove (a 42) 0 [0,1] d42 b11
  have b12 : a 44 ≠ 0 := exclude [1] (fun u v => edge r132 v u) (a 44) (a 42) 0 t11 c132 (by decide +kernel)
  have t12 : a 44 ∈ [1] := remove (a 44) 0 [0,1] d44 b12
  have b13 : a 36 ≠ 0 := exclude [1] (edge r115) (a 36) (a 44) 0 t12 c115 (by decide +kernel)
  have t13 : a 36 ∈ [1] := remove (a 36) 0 [0,1] d36 b13
  have b14 : a 50 ≠ 0 := exclude [1] (fun u v => edge r116 v u) (a 50) (a 36) 0 t13 c116 (by decide +kernel)
  have t14 : a 50 ∈ [2] := remove (a 50) 0 [0,2] d50 b14
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (t14))))))))))))))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0,1])
    (start12 : a 12 ∈ [0])
    (start13 : a 13 ∈ [0])
    (start14 : a 14 ∈ [0,1])
    (start15 : a 15 ∈ [0])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0])
    (start18 : a 18 ∈ [0,1,2,3])
    (start19 : a 19 ∈ [0])
    (start20 : a 20 ∈ [0])
    (start21 : a 21 ∈ [0,1,2,3])
    (start22 : a 22 ∈ [0,1])
    (start23 : a 23 ∈ [0,1])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0,1])
    (start26 : a 26 ∈ [0])
    (start27 : a 27 ∈ [0])
    (start28 : a 28 ∈ [0,1])
    (start29 : a 29 ∈ [0,1])
    (start30 : a 30 ∈ [0,1])
    (start31 : a 31 ∈ [0,1])
    (start32 : a 32 ∈ [0])
    (start33 : a 33 ∈ [0])
    (start34 : a 34 ∈ [0])
    (start35 : a 35 ∈ [0])
    (start36 : a 36 ∈ [0,1])
    (start37 : a 37 ∈ [0])
    (start38 : a 38 ∈ [0])
    (start39 : a 39 ∈ [0,1])
    (start40 : a 40 ∈ [0])
    (start41 : a 41 ∈ [0,1])
    (start42 : a 42 ∈ [0,1])
    (start43 : a 43 ∈ [0])
    (start44 : a 44 ∈ [0,1])
    (start45 : a 45 ∈ [0,1,2,3])
    (start46 : a 46 ∈ [0,1,2,3])
    (start47 : a 47 ∈ [0])
    (start48 : a 48 ∈ [0,1])
    (start49 : a 49 ∈ [0])
    (start50 : a 50 ∈ [0,1,2,3])
    (start51 : a 51 ∈ [0,1])
    (start52 : a 52 ∈ [0])
    (start53 : a 53 ∈ [0,1])
    (start54 : a 54 ∈ [0,1])
    (start55 : a 55 ∈ [0,1])
    (start56 : a 56 ∈ [0])
    (start57 : a 57 ∈ [0])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c5 : edge r5 (a 0) (a 29)=true)
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 9)=true)
    (c9 : edge r9 (a 1) (a 17)=true)
    (c10 : edge r10 (a 1) (a 30)=true)
    (c11 : edge r11 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 18)=true)
    (c15 : edge r15 (a 2) (a 31)=true)
    (c16 : edge r16 (a 3) (a 7)=true)
    (c17 : edge r17 (a 3) (a 11)=true)
    (c18 : edge r18 (a 3) (a 19)=true)
    (c19 : edge r19 (a 3) (a 32)=true)
    (c20 : edge r20 (a 4) (a 5)=true)
    (c21 : edge r21 (a 4) (a 6)=true)
    (c22 : edge r22 (a 4) (a 12)=true)
    (c23 : edge r23 (a 4) (a 20)=true)
    (c24 : edge r24 (a 4) (a 33)=true)
    (c25 : edge r25 (a 5) (a 7)=true)
    (c26 : edge r26 (a 5) (a 13)=true)
    (c27 : edge r27 (a 5) (a 21)=true)
    (c28 : edge r28 (a 5) (a 34)=true)
    (c29 : edge r29 (a 6) (a 7)=true)
    (c30 : edge r30 (a 6) (a 14)=true)
    (c31 : edge r31 (a 6) (a 22)=true)
    (c32 : edge r32 (a 6) (a 35)=true)
    (c33 : edge r33 (a 7) (a 15)=true)
    (c34 : edge r34 (a 7) (a 36)=true)
    (c35 : edge r35 (a 8) (a 9)=true)
    (c36 : edge r36 (a 8) (a 10)=true)
    (c37 : edge r37 (a 8) (a 12)=true)
    (c38 : edge r38 (a 8) (a 23)=true)
    (c39 : edge r39 (a 8) (a 37)=true)
    (c40 : edge r40 (a 9) (a 11)=true)
    (c41 : edge r41 (a 9) (a 13)=true)
    (c42 : edge r42 (a 9) (a 24)=true)
    (c43 : edge r43 (a 9) (a 38)=true)
    (c44 : edge r44 (a 10) (a 11)=true)
    (c45 : edge r45 (a 10) (a 14)=true)
    (c46 : edge r46 (a 10) (a 39)=true)
    (c47 : edge r47 (a 11) (a 15)=true)
    (c48 : edge r48 (a 11) (a 25)=true)
    (c49 : edge r49 (a 11) (a 40)=true)
    (c50 : edge r50 (a 12) (a 13)=true)
    (c51 : edge r51 (a 12) (a 14)=true)
    (c52 : edge r52 (a 12) (a 26)=true)
    (c53 : edge r53 (a 12) (a 41)=true)
    (c54 : edge r54 (a 13) (a 15)=true)
    (c55 : edge r55 (a 13) (a 42)=true)
    (c56 : edge r56 (a 14) (a 15)=true)
    (c57 : edge r57 (a 14) (a 27)=true)
    (c58 : edge r58 (a 14) (a 43)=true)
    (c59 : edge r59 (a 15) (a 28)=true)
    (c60 : edge r60 (a 15) (a 44)=true)
    (c61 : edge r61 (a 16) (a 17)=true)
    (c62 : edge r62 (a 16) (a 18)=true)
    (c63 : edge r63 (a 16) (a 20)=true)
    (c64 : edge r64 (a 16) (a 23)=true)
    (c65 : edge r65 (a 17) (a 19)=true)
    (c66 : edge r66 (a 17) (a 21)=true)
    (c67 : edge r67 (a 17) (a 24)=true)
    (c68 : edge r68 (a 17) (a 45)=true)
    (c69 : edge r69 (a 18) (a 19)=true)
    (c70 : edge r70 (a 18) (a 22)=true)
    (c71 : edge r71 (a 18) (a 46)=true)
    (c72 : edge r72 (a 19) (a 25)=true)
    (c73 : edge r73 (a 19) (a 47)=true)
    (c74 : edge r74 (a 20) (a 21)=true)
    (c75 : edge r75 (a 20) (a 22)=true)
    (c76 : edge r76 (a 20) (a 26)=true)
    (c77 : edge r77 (a 20) (a 48)=true)
    (c78 : edge r78 (a 21) (a 49)=true)
    (c79 : edge r79 (a 22) (a 27)=true)
    (c80 : edge r80 (a 23) (a 24)=true)
    (c81 : edge r81 (a 23) (a 26)=true)
    (c82 : edge r82 (a 23) (a 51)=true)
    (c83 : edge r83 (a 24) (a 25)=true)
    (c84 : edge r84 (a 24) (a 52)=true)
    (c85 : edge r85 (a 25) (a 28)=true)
    (c86 : edge r86 (a 25) (a 54)=true)
    (c87 : edge r87 (a 26) (a 27)=true)
    (c88 : edge r88 (a 26) (a 55)=true)
    (c89 : edge r89 (a 27) (a 28)=true)
    (c90 : edge r90 (a 27) (a 57)=true)
    (c91 : edge r91 (a 29) (a 30)=true)
    (c92 : edge r92 (a 29) (a 31)=true)
    (c93 : edge r93 (a 29) (a 33)=true)
    (c94 : edge r94 (a 29) (a 37)=true)
    (c95 : edge r95 (a 30) (a 32)=true)
    (c96 : edge r96 (a 30) (a 34)=true)
    (c97 : edge r97 (a 30) (a 38)=true)
    (c98 : edge r98 (a 30) (a 45)=true)
    (c99 : edge r99 (a 31) (a 32)=true)
    (c100 : edge r100 (a 31) (a 35)=true)
    (c101 : edge r101 (a 31) (a 39)=true)
    (c102 : edge r102 (a 31) (a 46)=true)
    (c103 : edge r103 (a 32) (a 36)=true)
    (c104 : edge r104 (a 32) (a 40)=true)
    (c105 : edge r105 (a 32) (a 47)=true)
    (c106 : edge r106 (a 33) (a 34)=true)
    (c107 : edge r107 (a 33) (a 35)=true)
    (c108 : edge r108 (a 33) (a 41)=true)
    (c109 : edge r109 (a 33) (a 48)=true)
    (c110 : edge r110 (a 34) (a 36)=true)
    (c111 : edge r111 (a 34) (a 42)=true)
    (c112 : edge r112 (a 34) (a 49)=true)
    (c113 : edge r113 (a 35) (a 36)=true)
    (c114 : edge r114 (a 35) (a 43)=true)
    (c115 : edge r115 (a 36) (a 44)=true)
    (c116 : edge r116 (a 36) (a 50)=true)
    (c117 : edge r117 (a 37) (a 38)=true)
    (c118 : edge r118 (a 37) (a 39)=true)
    (c119 : edge r119 (a 37) (a 41)=true)
    (c120 : edge r120 (a 37) (a 51)=true)
    (c121 : edge r121 (a 38) (a 40)=true)
    (c122 : edge r122 (a 38) (a 42)=true)
    (c123 : edge r123 (a 38) (a 52)=true)
    (c124 : edge r124 (a 39) (a 40)=true)
    (c125 : edge r125 (a 39) (a 43)=true)
    (c126 : edge r126 (a 39) (a 53)=true)
    (c127 : edge r127 (a 40) (a 44)=true)
    (c128 : edge r128 (a 40) (a 54)=true)
    (c129 : edge r129 (a 41) (a 42)=true)
    (c130 : edge r130 (a 41) (a 43)=true)
    (c131 : edge r131 (a 41) (a 55)=true)
    (c132 : edge r132 (a 42) (a 44)=true)
    (c133 : edge r133 (a 42) (a 56)=true)
    (c134 : edge r134 (a 43) (a 44)=true)
    (c135 : edge r135 (a 43) (a 57)=true)
    (c136 : edge r136 (a 45) (a 47)=true)
    (c137 : edge r137 (a 45) (a 49)=true)
    (c138 : edge r138 (a 45) (a 52)=true)
    (c139 : edge r139 (a 46) (a 47)=true)
    (c140 : edge r140 (a 46) (a 53)=true)
    (c141 : edge r141 (a 47) (a 50)=true)
    (c142 : edge r142 (a 47) (a 54)=true)
    (c143 : edge r143 (a 48) (a 49)=true)
    (c144 : edge r144 (a 48) (a 55)=true)
    (c145 : edge r145 (a 49) (a 50)=true)
    (c146 : edge r146 (a 49) (a 56)=true)
    (c147 : edge r147 (a 51) (a 52)=true)
    (c148 : edge r148 (a 51) (a 53)=true)
    (c149 : edge r149 (a 51) (a 55)=true)
    (c150 : edge r150 (a 52) (a 54)=true)
    (c151 : edge r151 (a 52) (a 56)=true)
    (c152 : edge r152 (a 53) (a 54)=true)
    (c153 : edge r153 (a 53) (a 57)=true)
    (c154 : edge r154 (a 55) (a 56)=true)
    (c155 : edge r155 (a 55) (a 57)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0 ∧ a 32=0 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=0 ∧ a 37=0 ∧ a 38=0 ∧ a 39=0 ∧ a 40=0 ∧ a 41=0 ∧ a 42=0 ∧ a 43=0 ∧ a 44=0 ∧ a 45=0 ∧ a 46=0 ∧ a 47=0 ∧ a 48=0 ∧ a 49=0 ∧ a 50=0 ∧ a 51=0 ∧ a 52=0 ∧ a 53=0 ∧ a 54=0 ∧ a 55=0 ∧ a 56=0 ∧ a 57=0) ∨
      (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=1 ∧ a 5=1 ∧ a 6=1 ∧ a 7=0 ∧ a 8=1 ∧ a 9=1 ∧ a 10=1 ∧ a 11=1 ∧ a 12=0 ∧ a 13=0 ∧ a 14=1 ∧ a 15=0 ∧ a 16=1 ∧ a 17=0 ∧ a 18=2 ∧ a 19=0 ∧ a 20=0 ∧ a 21=2 ∧ a 22=1 ∧ a 23=1 ∧ a 24=1 ∧ a 25=1 ∧ a 26=0 ∧ a 27=0 ∧ a 28=1 ∧ a 29=1 ∧ a 30=1 ∧ a 31=1 ∧ a 32=0 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=1 ∧ a 37=0 ∧ a 38=0 ∧ a 39=1 ∧ a 40=0 ∧ a 41=1 ∧ a 42=1 ∧ a 43=0 ∧ a 44=1 ∧ a 45=2 ∧ a 46=2 ∧ a 47=0 ∧ a 48=1 ∧ a 49=0 ∧ a 50=2 ∧ a 51=1 ∧ a 52=0 ∧ a 53=1 ∧ a 54=1 ∧ a 55=1 ∧ a 56=0 ∧ a 57=0) := by
  have group1 := chunk0 a start18 start2 start21 start17 start45 start46 start50 start47 c14 c66 c68 c71 c141
  rcases group1 with ⟨h2,h3,h4,h5,h6⟩
  rcases (show a 4=0 ∨ a 4=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start4) with q7 | q8
  · have h9 : a 4 ∈ [0] := List.mem_singleton.mpr q7
    have group10 := chunk1 a start5 h9 start6 h3 start14 start22 start10 start39 h2 h5 start31 start53 start51 start55 start54 start8 start23 c20 c21 c27 c30 c31 c36 c38 c45 c46 c70 c71 c101 c126 c148 c149 c152
    rcases group10 with ⟨h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
    have group27 := chunk2 a start11 h16 start25 start16 h18 start24 h26 start28 start29 h20 start41 h23 start48 start9 h25 start30 h4 start42 start44 start36 h6 c35 c44 c48 c62 c80 c85 c91 c92 c98 c115 c116 c129 c131 c132 c144
    rcases group27 with ⟨h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42⟩
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h9) (And.intro (forced (a 5) 0 h11) (And.intro (forced (a 6) 0 h12) (And.intro (forced (a 7) 0 start7) (And.intro (forced (a 8) 0 h25) (And.intro (forced (a 9) 0 h36) (And.intro (forced (a 10) 0 h16) (And.intro (forced (a 11) 0 h28) (And.intro (forced (a 12) 0 start12) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 0 h14) (And.intro (forced (a 15) 0 start15) (And.intro (forced (a 16) 0 h30) (And.intro (forced (a 17) 0 start17) (And.intro (forced (a 18) 0 h18) (And.intro (forced (a 19) 0 start19) (And.intro (forced (a 20) 0 start20) (And.intro (forced (a 21) 0 h13) (And.intro (forced (a 22) 0 h15) (And.intro (forced (a 23) 0 h26) (And.intro (forced (a 24) 0 h31) (And.intro (forced (a 25) 0 h29) (And.intro (forced (a 26) 0 start26) (And.intro (forced (a 27) 0 start27) (And.intro (forced (a 28) 0 h32) (And.intro (forced (a 29) 0 h33) (And.intro (forced (a 30) 0 h37) (And.intro (forced (a 31) 0 h20) (And.intro (forced (a 32) 0 start32) (And.intro (forced (a 33) 0 start33) (And.intro (forced (a 34) 0 start34) (And.intro (forced (a 35) 0 start35) (And.intro (forced (a 36) 0 h41) (And.intro (forced (a 37) 0 start37) (And.intro (forced (a 38) 0 start38) (And.intro (forced (a 39) 0 h17) (And.intro (forced (a 40) 0 start40) (And.intro (forced (a 41) 0 h34) (And.intro (forced (a 42) 0 h39) (And.intro (forced (a 43) 0 start43) (And.intro (forced (a 44) 0 h40) (And.intro (forced (a 45) 0 h38) (And.intro (forced (a 46) 0 h19) (And.intro (forced (a 47) 0 start47) (And.intro (forced (a 48) 0 h35) (And.intro (forced (a 49) 0 start49) (And.intro (forced (a 50) 0 h42) (And.intro (forced (a 51) 0 h22) (And.intro (forced (a 52) 0 start52) (And.intro (forced (a 53) 0 h21) (And.intro (forced (a 54) 0 h24) (And.intro (forced (a 55) 0 h23) (And.intro (forced (a 56) 0 start56) (forced (a 57) 0 start57))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · have h43 : a 4 ∈ [1] := List.mem_singleton.mpr q8
    have group44 := chunk3 a start5 h43 start6 h3 start14 start22 start10 start39 h2 h5 start31 start53 start51 start55 start54 start8 start23 c20 c21 c27 c30 c31 c36 c38 c45 c46 c70 c71 c101 c126 c148 c149 c152
    rcases group44 with ⟨h45,h46,h47,h48,h49,h50,h51,h52,h53,h54,h55,h56,h57,h58,h59,h60⟩
    have group61 := chunk4 a start11 h50 start25 start16 h52 start24 h60 start28 start29 h54 start41 h57 start48 start9 h59 start30 h4 start42 start44 start36 h6 c35 c44 c48 c62 c80 c85 c91 c92 c98 c115 c116 c129 c131 c132 c144
    rcases group61 with ⟨h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74,h75,h76⟩
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 1 h43) (And.intro (forced (a 5) 1 h45) (And.intro (forced (a 6) 1 h46) (And.intro (forced (a 7) 0 start7) (And.intro (forced (a 8) 1 h59) (And.intro (forced (a 9) 1 h70) (And.intro (forced (a 10) 1 h50) (And.intro (forced (a 11) 1 h62) (And.intro (forced (a 12) 0 start12) (And.intro (forced (a 13) 0 start13) (And.intro (forced (a 14) 1 h48) (And.intro (forced (a 15) 0 start15) (And.intro (forced (a 16) 1 h64) (And.intro (forced (a 17) 0 start17) (And.intro (forced (a 18) 2 h52) (And.intro (forced (a 19) 0 start19) (And.intro (forced (a 20) 0 start20) (And.intro (forced (a 21) 2 h47) (And.intro (forced (a 22) 1 h49) (And.intro (forced (a 23) 1 h60) (And.intro (forced (a 24) 1 h65) (And.intro (forced (a 25) 1 h63) (And.intro (forced (a 26) 0 start26) (And.intro (forced (a 27) 0 start27) (And.intro (forced (a 28) 1 h66) (And.intro (forced (a 29) 1 h67) (And.intro (forced (a 30) 1 h71) (And.intro (forced (a 31) 1 h54) (And.intro (forced (a 32) 0 start32) (And.intro (forced (a 33) 0 start33) (And.intro (forced (a 34) 0 start34) (And.intro (forced (a 35) 0 start35) (And.intro (forced (a 36) 1 h75) (And.intro (forced (a 37) 0 start37) (And.intro (forced (a 38) 0 start38) (And.intro (forced (a 39) 1 h51) (And.intro (forced (a 40) 0 start40) (And.intro (forced (a 41) 1 h68) (And.intro (forced (a 42) 1 h73) (And.intro (forced (a 43) 0 start43) (And.intro (forced (a 44) 1 h74) (And.intro (forced (a 45) 2 h72) (And.intro (forced (a 46) 2 h53) (And.intro (forced (a 47) 0 start47) (And.intro (forced (a 48) 1 h69) (And.intro (forced (a 49) 0 start49) (And.intro (forced (a 50) 2 h76) (And.intro (forced (a 51) 1 h56) (And.intro (forced (a 52) 0 start52) (And.intro (forced (a 53) 1 h55) (And.intro (forced (a 54) 1 h58) (And.intro (forced (a 55) 1 h57) (And.intro (forced (a 56) 0 start56) (forced (a 57) 0 start57))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_218
