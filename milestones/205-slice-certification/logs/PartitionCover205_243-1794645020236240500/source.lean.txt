import FiniteDomain205
namespace PartitionCover205_243
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[1]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[1]
def r5 : Array Nat := #[3]
def r6 : Array Nat := #[3]
def r7 : Array Nat := #[3]
def r8 : Array Nat := #[3]
def r9 : Array Nat := #[1]
def r10 : Array Nat := #[1,2]
def r11 : Array Nat := #[1,1]
def r12 : Array Nat := #[1,2]
def r13 : Array Nat := #[1,2]
def r14 : Array Nat := #[1,2]
def r15 : Array Nat := #[1,1]
def r16 : Array Nat := #[1,2]
def r17 : Array Nat := #[1,2]
def r18 : Array Nat := #[1,2]
def r19 : Array Nat := #[1,1]
def r20 : Array Nat := #[1,2]
def r21 : Array Nat := #[1,2]
def r22 : Array Nat := #[1,2]
def r23 : Array Nat := #[1]
def r24 : Array Nat := #[3]
def r25 : Array Nat := #[1]
def r26 : Array Nat := #[1]
def r27 : Array Nat := #[1]
def r28 : Array Nat := #[3]
def r29 : Array Nat := #[3]
def r30 : Array Nat := #[1,2]
def r31 : Array Nat := #[1,2]
def r32 : Array Nat := #[1,1]
def r33 : Array Nat := #[1,2]
def r34 : Array Nat := #[1,2]
def r35 : Array Nat := #[1,2]
def r36 : Array Nat := #[1,2]
def r37 : Array Nat := #[1,2]
def r38 : Array Nat := #[1,2]
def r39 : Array Nat := #[1,2]
def r40 : Array Nat := #[1,2]
def r41 : Array Nat := #[1,2]
def r42 : Array Nat := #[1,2]
def r43 : Array Nat := #[1,1]
def r44 : Array Nat := #[1,2]
def r45 : Array Nat := #[1,2]
def r46 : Array Nat := #[3]
def r47 : Array Nat := #[3]
def r48 : Array Nat := #[1]
def r49 : Array Nat := #[1]
def r50 : Array Nat := #[1,1]
def r51 : Array Nat := #[1,1]
def r52 : Array Nat := #[1,2]
def r53 : Array Nat := #[1,1]
def r54 : Array Nat := #[1,2]
def r55 : Array Nat := #[1,1]
def r56 : Array Nat := #[1]
def r57 : Array Nat := #[1]
def r58 : Array Nat := #[1,1,2,2]
def r59 : Array Nat := #[1,0,2,0]
def r60 : Array Nat := #[1,2,4,8]
def r61 : Array Nat := #[1,0,2,0]
def r62 : Array Nat := #[1,0,2,0]
def r63 : Array Nat := #[1,2]
def r64 : Array Nat := #[1,2]
def r65 : Array Nat := #[1,2]
def r66 : Array Nat := #[1,2]
def r67 : Array Nat := #[1,2]
def r68 : Array Nat := #[1,1]
def r69 : Array Nat := #[1,2]
def r70 : Array Nat := #[1,4]
def r71 : Array Nat := #[1,2]
def r72 : Array Nat := #[1,2]
def r73 : Array Nat := #[1,2]
def r74 : Array Nat := #[1,1,2,2]
def r75 : Array Nat := #[1,0,1,0]
def r76 : Array Nat := #[1,0,1,0]
def r77 : Array Nat := #[1,0,1,0]
def r78 : Array Nat := #[1,2]
def r79 : Array Nat := #[1,1]
def r80 : Array Nat := #[1,1]
def r81 : Array Nat := #[3]
def r82 : Array Nat := #[3]
def r83 : Array Nat := #[5]
def r84 : Array Nat := #[1,1]
def r85 : Array Nat := #[1,2]
def r86 : Array Nat := #[1,2]
def r87 : Array Nat := #[1,2]
def r88 : Array Nat := #[1,1]
def r89 : Array Nat := #[1,2]
def r90 : Array Nat := #[1,2]
def r91 : Array Nat := #[1,1]
def r92 : Array Nat := #[1,2]
def r93 : Array Nat := #[1,2]
def r94 : Array Nat := #[1,2]
def r95 : Array Nat := #[1,2]
def r96 : Array Nat := #[1,1]
def r97 : Array Nat := #[1,2]
def r98 : Array Nat := #[1]
def r99 : Array Nat := #[3]
def r100 : Array Nat := #[3]
def r101 : Array Nat := #[1]
def r102 : Array Nat := #[1]
def r103 : Array Nat := #[1,1]
def r104 : Array Nat := #[1,2]
def r105 : Array Nat := #[1]
def r106 : Array Nat := #[1,1]
def r107 : Array Nat := #[1,2]
def r108 : Array Nat := #[1,2]
def r109 : Array Nat := #[1,2]
def r110 : Array Nat := #[1,2]
def r111 : Array Nat := #[3]
def r112 : Array Nat := #[3]
def r113 : Array Nat := #[3]
def r114 : Array Nat := #[3]
def r115 : Array Nat := #[1,2]
def r116 : Array Nat := #[1,1]
def r117 : Array Nat := #[1,2]
def r118 : Array Nat := #[1,4]
def r119 : Array Nat := #[1,2]
def r120 : Array Nat := #[1,2]
def r121 : Array Nat := #[1,2]
def r122 : Array Nat := #[1,2]
def r123 : Array Nat := #[1,1]
def r124 : Array Nat := #[1,1]
def r125 : Array Nat := #[1,1]
def r126 : Array Nat := #[1,2]
def r127 : Array Nat := #[1,2]
def r128 : Array Nat := #[1,1]
def r129 : Array Nat := #[3]
def r130 : Array Nat := #[1]
def r131 : Array Nat := #[5]
def r132 : Array Nat := #[1,1]
def r133 : Array Nat := #[1,2]
def r134 : Array Nat := #[1,2]
def r135 : Array Nat := #[1,2]
def r136 : Array Nat := #[1,1]
def r137 : Array Nat := #[1,2]
def r138 : Array Nat := #[1,2]
def r139 : Array Nat := #[1,2]
def r140 : Array Nat := #[1,2]
def r141 : Array Nat := #[1,2]
def r142 : Array Nat := #[1,1]
def r143 : Array Nat := #[1,2]
def r144 : Array Nat := #[1,1]
def r145 : Array Nat := #[1,2]
def r146 : Array Nat := #[3]
def r147 : Array Nat := #[1]
def r148 : Array Nat := #[3]
def r149 : Array Nat := #[1,1]
def r150 : Array Nat := #[1,1]
def r151 : Array Nat := #[1]
def r152 : Array Nat := #[3]
def r153 : Array Nat := #[1]
def r154 : Array Nat := #[1,2]
def r155 : Array Nat := #[1,4]
def r156 : Array Nat := #[1,1]
def r157 : Array Nat := #[1,2]
def r158 : Array Nat := #[1,2]
def r159 : Array Nat := #[1,1]
def r160 : Array Nat := #[1,2]
def r161 : Array Nat := #[1,1,2,2]
def r162 : Array Nat := #[1,2,4,8]
def r163 : Array Nat := #[1,0,2,0]
def r164 : Array Nat := #[1,2]
def r165 : Array Nat := #[1,2]
def r166 : Array Nat := #[1]
def r167 : Array Nat := #[5]
def r168 : Array Nat := #[3]
def r169 : Array Nat := #[3]
def r170 : Array Nat := #[1]
def r171 : Array Nat := #[1,1,2,2]
def r172 : Array Nat := #[1,0,2,0]
def r173 : Array Nat := #[1,1]
def r174 : Array Nat := #[1,2]
def r175 : Array Nat := #[1,2]
def r176 : Array Nat := #[1,2]
def r177 : Array Nat := #[1,2]
def r178 : Array Nat := #[1,1]
def r179 : Array Nat := #[1,2]
def r180 : Array Nat := #[1,2]
def r181 : Array Nat := #[1,1]
def r182 : Array Nat := #[1,1]
def r183 : Array Nat := #[1,2]
def r184 : Array Nat := #[1]
def r185 : Array Nat := #[1,1]
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d0 : a 0 ∈ [0])
    (d7 : a 7 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1])
    (d3 : a 3 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d33 : a 33 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d34 : a 34 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d39 : a 39 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 7)=true)
    (c3 : edge r3 (a 0) (a 15)=true)
    (c4 : edge r4 (a 0) (a 31)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 9)=true)
    (c13 : edge r13 (a 2) (a 17)=true)
    (c14 : edge r14 (a 2) (a 33)=true)
    (c16 : edge r16 (a 3) (a 10)=true)
    (c17 : edge r17 (a 3) (a 18)=true)
    (c18 : edge r18 (a 3) (a 34)=true)
    (c30 : edge r30 (a 7) (a 8)=true)
    (c33 : edge r33 (a 7) (a 23)=true)
    (c34 : edge r34 (a 7) (a 39)=true)
    : a 2 ∈ [0] ∧ a 7 ∈ [0] ∧ a 15 ∈ [0] ∧ a 31 ∈ [0] ∧ a 3 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 33 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 34 ∈ [0] ∧ a 8 ∈ [0] ∧ a 23 ∈ [0] ∧ a 39 ∈ [0] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 7 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 7) (a 0) 1 d0 c2 (by decide +kernel)
  have t1 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b1
  have b2 : a 15 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 15) (a 0) 1 d0 c3 (by decide +kernel)
  have t2 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b2
  have b3 : a 15 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 15) (a 0) 2 d0 c3 (by decide +kernel)
  have t3 : a 15 ∈ [0,3] := remove (a 15) 2 [0,2,3] t2 b3
  have b4 : a 15 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 15) (a 0) 3 d0 c3 (by decide +kernel)
  have t4 : a 15 ∈ [0] := remove (a 15) 3 [0,3] t3 b4
  have b5 : a 31 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 31) (a 0) 1 d0 c4 (by decide +kernel)
  have t5 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b5
  have b6 : a 3 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 3) (a 2) 1 t0 c10 (by decide +kernel)
  have t6 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b6
  have b7 : a 9 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 9) (a 2) 1 t0 c12 (by decide +kernel)
  have t7 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b7
  have b8 : a 17 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 17) (a 2) 1 t0 c13 (by decide +kernel)
  have t8 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b8
  have b9 : a 33 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 33) (a 2) 1 t0 c14 (by decide +kernel)
  have t9 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b9
  have b10 : a 10 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 10) (a 3) 1 t6 c16 (by decide +kernel)
  have t10 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b10
  have b11 : a 18 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 18) (a 3) 1 t6 c17 (by decide +kernel)
  have t11 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b11
  have b12 : a 34 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 34) (a 3) 1 t6 c18 (by decide +kernel)
  have t12 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b12
  have b13 : a 8 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 8) (a 7) 1 t1 c30 (by decide +kernel)
  have t13 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b13
  have b14 : a 23 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 23) (a 7) 1 t1 c33 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b14
  have b15 : a 39 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 39) (a 7) 1 t1 c34 (by decide +kernel)
  have t15 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b15
  exact And.intro t0 (And.intro t1 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))

theorem chunk1 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d42 : a 42 ∈ [0,1])
    (d44 : a 44 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3])
    (d47 : a 47 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (c36 : edge r36 (a 8) (a 12)=true)
    (c37 : edge r37 (a 8) (a 24)=true)
    (c38 : edge r38 (a 8) (a 40)=true)
    (c40 : edge r40 (a 9) (a 13)=true)
    (c41 : edge r41 (a 9) (a 25)=true)
    (c42 : edge r42 (a 9) (a 41)=true)
    (c44 : edge r44 (a 10) (a 26)=true)
    (c45 : edge r45 (a 10) (a 42)=true)
    (c52 : edge r52 (a 12) (a 44)=true)
    (c54 : edge r54 (a 13) (a 29)=true)
    (c58 : edge r58 (a 15) (a 16)=true)
    (c60 : edge r60 (a 15) (a 19)=true)
    (c62 : edge r62 (a 15) (a 47)=true)
    (c64 : edge r64 (a 16) (a 20)=true)
    : a 12 ∈ [0] ∧ a 24 ∈ [0] ∧ a 40 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 41 ∈ [0] ∧ a 26 ∈ [0] ∧ a 42 ∈ [0] ∧ a 44 ∈ [0] ∧ a 29 ∈ [0] ∧ a 16 ∈ [0] ∧ a 19 ∈ [0] ∧ a 47 ∈ [0] ∧ a 20 ∈ [0] := by
  have b0 : a 12 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 12) (a 8) 1 d8 c36 (by decide +kernel)
  have t0 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b0
  have b1 : a 24 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 24) (a 8) 1 d8 c37 (by decide +kernel)
  have t1 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b1
  have b2 : a 40 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 40) (a 8) 1 d8 c38 (by decide +kernel)
  have t2 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b2
  have b3 : a 13 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 9) 1 d9 c40 (by decide +kernel)
  have t3 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b3
  have b4 : a 25 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 25) (a 9) 1 d9 c41 (by decide +kernel)
  have t4 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b4
  have b5 : a 41 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 41) (a 9) 1 d9 c42 (by decide +kernel)
  have t5 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b5
  have b6 : a 26 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 26) (a 10) 1 d10 c44 (by decide +kernel)
  have t6 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b6
  have b7 : a 42 ≠ 1 := exclude [0] (fun u v => edge r45 v u) (a 42) (a 10) 1 d10 c45 (by decide +kernel)
  have t7 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b7
  have b8 : a 44 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 44) (a 12) 1 t0 c52 (by decide +kernel)
  have t8 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b8
  have b9 : a 29 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 29) (a 13) 1 t3 c54 (by decide +kernel)
  have t9 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b9
  have b10 : a 16 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 16) (a 15) 1 d15 c58 (by decide +kernel)
  have t10 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b10
  have b11 : a 19 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 19) (a 15) 1 d15 c60 (by decide +kernel)
  have t11 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b11
  have b12 : a 19 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 19) (a 15) 2 d15 c60 (by decide +kernel)
  have t12 : a 19 ∈ [0,3] := remove (a 19) 2 [0,2,3] t11 b12
  have b13 : a 19 ≠ 3 := exclude [0] (fun u v => edge r60 v u) (a 19) (a 15) 3 d15 c60 (by decide +kernel)
  have t13 : a 19 ∈ [0] := remove (a 19) 3 [0,3] t12 b13
  have b14 : a 47 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 47) (a 15) 1 d15 c62 (by decide +kernel)
  have t14 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b14
  have b15 : a 20 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 20) (a 16) 1 t10 c64 (by decide +kernel)
  have t15 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t13 (And.intro t14 (t15)))))))))))))

theorem chunk2 (a : Nat → Nat)
    (d48 : a 48 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (d49 : a 49 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0])
    (d22 : a 22 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d53 : a 53 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0])
    (d54 : a 54 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d56 : a 56 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d57 : a 57 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d58 : a 58 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d61 : a 61 ∈ [0,1])
    (d29 : a 29 ∈ [0])
    (d35 : a 35 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d38 : a 38 ∈ [0,1])
    (d34 : a 34 ∈ [0])
    (c66 : edge r66 (a 16) (a 48)=true)
    (c70 : edge r70 (a 17) (a 49)=true)
    (c71 : edge r71 (a 18) (a 22)=true)
    (c73 : edge r73 (a 18) (a 50)=true)
    (c83 : edge r83 (a 21) (a 53)=true)
    (c85 : edge r85 (a 22) (a 54)=true)
    (c89 : edge r89 (a 23) (a 55)=true)
    (c92 : edge r92 (a 24) (a 56)=true)
    (c95 : edge r95 (a 25) (a 57)=true)
    (c97 : edge r97 (a 26) (a 58)=true)
    (c104 : edge r104 (a 29) (a 61)=true)
    (c108 : edge r108 (a 31) (a 35)=true)
    (c119 : edge r119 (a 34) (a 38)=true)
    : a 48 ∈ [0] ∧ a 49 ∈ [0] ∧ a 22 ∈ [0] ∧ a 50 ∈ [0] ∧ a 53 ∈ [0,2] ∧ a 54 ∈ [0] ∧ a 55 ∈ [0] ∧ a 56 ∈ [0] ∧ a 57 ∈ [0] ∧ a 58 ∈ [0] ∧ a 61 ∈ [0] ∧ a 35 ∈ [0] ∧ a 38 ∈ [0] := by
  have b0 : a 48 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 48) (a 16) 1 d16 c66 (by decide +kernel)
  have t0 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b0
  have b1 : a 49 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 49) (a 17) 1 d17 c70 (by decide +kernel)
  have t1 : a 49 ∈ [0,2,3] := remove (a 49) 1 [0,1,2,3] d49 b1
  have b2 : a 49 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 49) (a 17) 2 d17 c70 (by decide +kernel)
  have t2 : a 49 ∈ [0,3] := remove (a 49) 2 [0,2,3] t1 b2
  have b3 : a 49 ≠ 3 := exclude [0] (fun u v => edge r70 v u) (a 49) (a 17) 3 d17 c70 (by decide +kernel)
  have t3 : a 49 ∈ [0] := remove (a 49) 3 [0,3] t2 b3
  have b4 : a 22 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 22) (a 18) 1 d18 c71 (by decide +kernel)
  have t4 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b4
  have b5 : a 50 ≠ 1 := exclude [0] (fun u v => edge r73 v u) (a 50) (a 18) 1 d18 c73 (by decide +kernel)
  have t5 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b5
  have b6 : a 53 ≠ 1 := exclude [0] (fun u v => edge r83 v u) (a 53) (a 21) 1 d21 c83 (by decide +kernel)
  have t6 : a 53 ∈ [0,2,3] := remove (a 53) 1 [0,1,2,3] d53 b6
  have b7 : a 53 ≠ 3 := exclude [0] (fun u v => edge r83 v u) (a 53) (a 21) 3 d21 c83 (by decide +kernel)
  have t7 : a 53 ∈ [0,2] := remove (a 53) 3 [0,2,3] t6 b7
  have b8 : a 54 ≠ 1 := exclude [0] (fun u v => edge r85 v u) (a 54) (a 22) 1 t4 c85 (by decide +kernel)
  have t8 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b8
  have b9 : a 55 ≠ 1 := exclude [0] (fun u v => edge r89 v u) (a 55) (a 23) 1 d23 c89 (by decide +kernel)
  have t9 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b9
  have b10 : a 56 ≠ 1 := exclude [0] (fun u v => edge r92 v u) (a 56) (a 24) 1 d24 c92 (by decide +kernel)
  have t10 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b10
  have b11 : a 57 ≠ 1 := exclude [0] (fun u v => edge r95 v u) (a 57) (a 25) 1 d25 c95 (by decide +kernel)
  have t11 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b11
  have b12 : a 58 ≠ 1 := exclude [0] (fun u v => edge r97 v u) (a 58) (a 26) 1 d26 c97 (by decide +kernel)
  have t12 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b12
  have b13 : a 61 ≠ 1 := exclude [0] (fun u v => edge r104 v u) (a 61) (a 29) 1 d29 c104 (by decide +kernel)
  have t13 : a 61 ∈ [0] := remove (a 61) 1 [0,1] d61 b13
  have b14 : a 35 ≠ 1 := exclude [0] (fun u v => edge r108 v u) (a 35) (a 31) 1 d31 c108 (by decide +kernel)
  have t14 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b14
  have b15 : a 38 ≠ 1 := exclude [0] (fun u v => edge r119 v u) (a 38) (a 34) 1 d34 c119 (by decide +kernel)
  have t15 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b15
  exact And.intro t0 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))))))

theorem chunk3 (a : Nat → Nat)
    (d36 : a 36 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (d53 : a 53 ∈ [0,2])
    (d49 : a 49 ∈ [0])
    (d59 : a 59 ∈ [0,1])
    (d55 : a 55 ∈ [0])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (c20 : edge r20 (a 4) (a 12)=true)
    (c122 : edge r122 (a 35) (a 36)=true)
    (c162 : edge r162 (a 49) (a 53)=true)
    (c176 : edge r176 (a 55) (a 59)=true)
    : a 36 ∈ [0] ∧ a 53 ∈ [0] ∧ a 59 ∈ [0] ∧ a 4 ∈ [0] := by
  have b0 : a 36 ≠ 1 := exclude [0] (fun u v => edge r122 v u) (a 36) (a 35) 1 d35 c122 (by decide +kernel)
  have t0 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b0
  have b1 : a 53 ≠ 2 := exclude [0] (fun u v => edge r162 v u) (a 53) (a 49) 2 d49 c162 (by decide +kernel)
  have t1 : a 53 ∈ [0] := remove (a 53) 2 [0,2] d53 b1
  have b2 : a 59 ≠ 1 := exclude [0] (fun u v => edge r176 v u) (a 59) (a 55) 1 d55 c176 (by decide +kernel)
  have t2 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b2
  have b3 : a 4 ≠ 1 := exclude [0] (edge r20) (a 4) (a 12) 1 d12 c20 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b3
  exact And.intro t0 (And.intro t1 (And.intro t2 (t3)))
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0,1])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1])
    (start14 : a 14 ∈ [0])
    (start15 : a 15 ∈ [0,1,2,3])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0,1])
    (start19 : a 19 ∈ [0,1,2,3])
    (start20 : a 20 ∈ [0,1])
    (start21 : a 21 ∈ [0])
    (start22 : a 22 ∈ [0,1])
    (start23 : a 23 ∈ [0,1])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0,1])
    (start26 : a 26 ∈ [0,1])
    (start27 : a 27 ∈ [0])
    (start28 : a 28 ∈ [0])
    (start29 : a 29 ∈ [0,1])
    (start30 : a 30 ∈ [0])
    (start31 : a 31 ∈ [0,1])
    (start32 : a 32 ∈ [0])
    (start33 : a 33 ∈ [0,1])
    (start34 : a 34 ∈ [0,1])
    (start35 : a 35 ∈ [0,1])
    (start36 : a 36 ∈ [0,1])
    (start37 : a 37 ∈ [0])
    (start38 : a 38 ∈ [0,1])
    (start39 : a 39 ∈ [0,1])
    (start40 : a 40 ∈ [0,1])
    (start41 : a 41 ∈ [0,1])
    (start42 : a 42 ∈ [0,1])
    (start43 : a 43 ∈ [0])
    (start44 : a 44 ∈ [0,1])
    (start45 : a 45 ∈ [0])
    (start46 : a 46 ∈ [0])
    (start47 : a 47 ∈ [0,1])
    (start48 : a 48 ∈ [0,1])
    (start49 : a 49 ∈ [0,1,2,3])
    (start50 : a 50 ∈ [0,1])
    (start51 : a 51 ∈ [0])
    (start52 : a 52 ∈ [0])
    (start53 : a 53 ∈ [0,1,2,3])
    (start54 : a 54 ∈ [0,1])
    (start55 : a 55 ∈ [0,1])
    (start56 : a 56 ∈ [0,1])
    (start57 : a 57 ∈ [0,1])
    (start58 : a 58 ∈ [0,1])
    (start59 : a 59 ∈ [0,1])
    (start60 : a 60 ∈ [0])
    (start61 : a 61 ∈ [0,1])
    (start62 : a 62 ∈ [0])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 7)=true)
    (c3 : edge r3 (a 0) (a 15)=true)
    (c4 : edge r4 (a 0) (a 31)=true)
    (c5 : edge r5 (a 1) (a 3)=true)
    (c6 : edge r6 (a 1) (a 4)=true)
    (c7 : edge r7 (a 1) (a 8)=true)
    (c8 : edge r8 (a 1) (a 16)=true)
    (c9 : edge r9 (a 1) (a 32)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 5)=true)
    (c12 : edge r12 (a 2) (a 9)=true)
    (c13 : edge r13 (a 2) (a 17)=true)
    (c14 : edge r14 (a 2) (a 33)=true)
    (c15 : edge r15 (a 3) (a 6)=true)
    (c16 : edge r16 (a 3) (a 10)=true)
    (c17 : edge r17 (a 3) (a 18)=true)
    (c18 : edge r18 (a 3) (a 34)=true)
    (c19 : edge r19 (a 4) (a 6)=true)
    (c20 : edge r20 (a 4) (a 12)=true)
    (c21 : edge r21 (a 4) (a 20)=true)
    (c22 : edge r22 (a 4) (a 36)=true)
    (c23 : edge r23 (a 5) (a 6)=true)
    (c24 : edge r24 (a 5) (a 13)=true)
    (c25 : edge r25 (a 5) (a 21)=true)
    (c26 : edge r26 (a 5) (a 37)=true)
    (c27 : edge r27 (a 6) (a 14)=true)
    (c28 : edge r28 (a 6) (a 22)=true)
    (c29 : edge r29 (a 6) (a 38)=true)
    (c30 : edge r30 (a 7) (a 8)=true)
    (c31 : edge r31 (a 7) (a 9)=true)
    (c32 : edge r32 (a 7) (a 11)=true)
    (c33 : edge r33 (a 7) (a 23)=true)
    (c34 : edge r34 (a 7) (a 39)=true)
    (c35 : edge r35 (a 8) (a 10)=true)
    (c36 : edge r36 (a 8) (a 12)=true)
    (c37 : edge r37 (a 8) (a 24)=true)
    (c38 : edge r38 (a 8) (a 40)=true)
    (c39 : edge r39 (a 9) (a 10)=true)
    (c40 : edge r40 (a 9) (a 13)=true)
    (c41 : edge r41 (a 9) (a 25)=true)
    (c42 : edge r42 (a 9) (a 41)=true)
    (c43 : edge r43 (a 10) (a 14)=true)
    (c44 : edge r44 (a 10) (a 26)=true)
    (c45 : edge r45 (a 10) (a 42)=true)
    (c46 : edge r46 (a 11) (a 12)=true)
    (c47 : edge r47 (a 11) (a 13)=true)
    (c48 : edge r48 (a 11) (a 27)=true)
    (c49 : edge r49 (a 11) (a 43)=true)
    (c50 : edge r50 (a 12) (a 14)=true)
    (c51 : edge r51 (a 12) (a 28)=true)
    (c52 : edge r52 (a 12) (a 44)=true)
    (c53 : edge r53 (a 13) (a 14)=true)
    (c54 : edge r54 (a 13) (a 29)=true)
    (c55 : edge r55 (a 13) (a 45)=true)
    (c56 : edge r56 (a 14) (a 30)=true)
    (c57 : edge r57 (a 14) (a 46)=true)
    (c58 : edge r58 (a 15) (a 16)=true)
    (c59 : edge r59 (a 15) (a 17)=true)
    (c60 : edge r60 (a 15) (a 19)=true)
    (c61 : edge r61 (a 15) (a 23)=true)
    (c62 : edge r62 (a 15) (a 47)=true)
    (c63 : edge r63 (a 16) (a 18)=true)
    (c64 : edge r64 (a 16) (a 20)=true)
    (c65 : edge r65 (a 16) (a 24)=true)
    (c66 : edge r66 (a 16) (a 48)=true)
    (c67 : edge r67 (a 17) (a 18)=true)
    (c68 : edge r68 (a 17) (a 21)=true)
    (c69 : edge r69 (a 17) (a 25)=true)
    (c70 : edge r70 (a 17) (a 49)=true)
    (c71 : edge r71 (a 18) (a 22)=true)
    (c72 : edge r72 (a 18) (a 26)=true)
    (c73 : edge r73 (a 18) (a 50)=true)
    (c74 : edge r74 (a 19) (a 20)=true)
    (c75 : edge r75 (a 19) (a 21)=true)
    (c76 : edge r76 (a 19) (a 27)=true)
    (c77 : edge r77 (a 19) (a 51)=true)
    (c78 : edge r78 (a 20) (a 22)=true)
    (c79 : edge r79 (a 20) (a 28)=true)
    (c80 : edge r80 (a 20) (a 52)=true)
    (c81 : edge r81 (a 21) (a 22)=true)
    (c82 : edge r82 (a 21) (a 29)=true)
    (c83 : edge r83 (a 21) (a 53)=true)
    (c84 : edge r84 (a 22) (a 30)=true)
    (c85 : edge r85 (a 22) (a 54)=true)
    (c86 : edge r86 (a 23) (a 24)=true)
    (c87 : edge r87 (a 23) (a 25)=true)
    (c88 : edge r88 (a 23) (a 27)=true)
    (c89 : edge r89 (a 23) (a 55)=true)
    (c90 : edge r90 (a 24) (a 26)=true)
    (c91 : edge r91 (a 24) (a 28)=true)
    (c92 : edge r92 (a 24) (a 56)=true)
    (c93 : edge r93 (a 25) (a 26)=true)
    (c94 : edge r94 (a 25) (a 29)=true)
    (c95 : edge r95 (a 25) (a 57)=true)
    (c96 : edge r96 (a 26) (a 30)=true)
    (c97 : edge r97 (a 26) (a 58)=true)
    (c98 : edge r98 (a 27) (a 28)=true)
    (c99 : edge r99 (a 27) (a 29)=true)
    (c100 : edge r100 (a 27) (a 59)=true)
    (c101 : edge r101 (a 28) (a 30)=true)
    (c102 : edge r102 (a 28) (a 60)=true)
    (c103 : edge r103 (a 29) (a 30)=true)
    (c104 : edge r104 (a 29) (a 61)=true)
    (c105 : edge r105 (a 30) (a 62)=true)
    (c106 : edge r106 (a 31) (a 32)=true)
    (c107 : edge r107 (a 31) (a 33)=true)
    (c108 : edge r108 (a 31) (a 35)=true)
    (c109 : edge r109 (a 31) (a 39)=true)
    (c110 : edge r110 (a 31) (a 47)=true)
    (c111 : edge r111 (a 32) (a 34)=true)
    (c112 : edge r112 (a 32) (a 36)=true)
    (c113 : edge r113 (a 32) (a 40)=true)
    (c114 : edge r114 (a 32) (a 48)=true)
    (c115 : edge r115 (a 33) (a 34)=true)
    (c116 : edge r116 (a 33) (a 37)=true)
    (c117 : edge r117 (a 33) (a 41)=true)
    (c118 : edge r118 (a 33) (a 49)=true)
    (c119 : edge r119 (a 34) (a 38)=true)
    (c120 : edge r120 (a 34) (a 42)=true)
    (c121 : edge r121 (a 34) (a 50)=true)
    (c122 : edge r122 (a 35) (a 36)=true)
    (c123 : edge r123 (a 35) (a 37)=true)
    (c124 : edge r124 (a 35) (a 43)=true)
    (c125 : edge r125 (a 35) (a 51)=true)
    (c126 : edge r126 (a 36) (a 38)=true)
    (c127 : edge r127 (a 36) (a 44)=true)
    (c128 : edge r128 (a 36) (a 52)=true)
    (c129 : edge r129 (a 37) (a 38)=true)
    (c130 : edge r130 (a 37) (a 45)=true)
    (c131 : edge r131 (a 37) (a 53)=true)
    (c132 : edge r132 (a 38) (a 46)=true)
    (c133 : edge r133 (a 38) (a 54)=true)
    (c134 : edge r134 (a 39) (a 40)=true)
    (c135 : edge r135 (a 39) (a 41)=true)
    (c136 : edge r136 (a 39) (a 43)=true)
    (c137 : edge r137 (a 39) (a 55)=true)
    (c138 : edge r138 (a 40) (a 42)=true)
    (c139 : edge r139 (a 40) (a 44)=true)
    (c140 : edge r140 (a 40) (a 56)=true)
    (c141 : edge r141 (a 41) (a 42)=true)
    (c142 : edge r142 (a 41) (a 45)=true)
    (c143 : edge r143 (a 41) (a 57)=true)
    (c144 : edge r144 (a 42) (a 46)=true)
    (c145 : edge r145 (a 42) (a 58)=true)
    (c146 : edge r146 (a 43) (a 44)=true)
    (c147 : edge r147 (a 43) (a 45)=true)
    (c148 : edge r148 (a 43) (a 59)=true)
    (c149 : edge r149 (a 44) (a 46)=true)
    (c150 : edge r150 (a 44) (a 60)=true)
    (c151 : edge r151 (a 45) (a 46)=true)
    (c152 : edge r152 (a 45) (a 61)=true)
    (c153 : edge r153 (a 46) (a 62)=true)
    (c154 : edge r154 (a 47) (a 48)=true)
    (c155 : edge r155 (a 47) (a 49)=true)
    (c156 : edge r156 (a 47) (a 51)=true)
    (c157 : edge r157 (a 47) (a 55)=true)
    (c158 : edge r158 (a 48) (a 50)=true)
    (c159 : edge r159 (a 48) (a 52)=true)
    (c160 : edge r160 (a 48) (a 56)=true)
    (c161 : edge r161 (a 49) (a 50)=true)
    (c162 : edge r162 (a 49) (a 53)=true)
    (c163 : edge r163 (a 49) (a 57)=true)
    (c164 : edge r164 (a 50) (a 54)=true)
    (c165 : edge r165 (a 50) (a 58)=true)
    (c166 : edge r166 (a 51) (a 52)=true)
    (c167 : edge r167 (a 51) (a 53)=true)
    (c168 : edge r168 (a 51) (a 59)=true)
    (c169 : edge r169 (a 52) (a 54)=true)
    (c170 : edge r170 (a 52) (a 60)=true)
    (c171 : edge r171 (a 53) (a 54)=true)
    (c172 : edge r172 (a 53) (a 61)=true)
    (c173 : edge r173 (a 54) (a 62)=true)
    (c174 : edge r174 (a 55) (a 56)=true)
    (c175 : edge r175 (a 55) (a 57)=true)
    (c176 : edge r176 (a 55) (a 59)=true)
    (c177 : edge r177 (a 56) (a 58)=true)
    (c178 : edge r178 (a 56) (a 60)=true)
    (c179 : edge r179 (a 57) (a 58)=true)
    (c180 : edge r180 (a 57) (a 61)=true)
    (c181 : edge r181 (a 58) (a 62)=true)
    (c182 : edge r182 (a 59) (a 60)=true)
    (c183 : edge r183 (a 59) (a 61)=true)
    (c184 : edge r184 (a 60) (a 62)=true)
    (c185 : edge r185 (a 61) (a 62)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0 ∧ a 32=0 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=0 ∧ a 37=0 ∧ a 38=0 ∧ a 39=0 ∧ a 40=0 ∧ a 41=0 ∧ a 42=0 ∧ a 43=0 ∧ a 44=0 ∧ a 45=0 ∧ a 46=0 ∧ a 47=0 ∧ a 48=0 ∧ a 49=0 ∧ a 50=0 ∧ a 51=0 ∧ a 52=0 ∧ a 53=0 ∧ a 54=0 ∧ a 55=0 ∧ a 56=0 ∧ a 57=0 ∧ a 58=0 ∧ a 59=0 ∧ a 60=0 ∧ a 61=0 ∧ a 62=0) := by
  have group1 := chunk0 a start2 start0 start7 start15 start31 start3 start9 start17 start33 start10 start18 start34 start8 start23 start39 c1 c2 c3 c4 c10 c12 c13 c14 c16 c17 c18 c30 c33 c34
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩
  have group16 := chunk1 a start12 h13 start24 start40 start13 h7 start25 start41 start26 h10 start42 start44 start29 start16 h4 start19 start47 start20 c36 c37 c38 c40 c41 c42 c44 c45 c52 c54 c58 c60 c62 c64
  rcases group16 with ⟨h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30⟩
  have group31 := chunk2 a start48 h27 start49 h8 start22 h11 start50 start53 start21 start54 start55 h14 start56 h18 start57 h21 start58 h23 start61 h26 start35 h5 start38 h12 c66 c70 c71 c73 c83 c85 c89 c92 c95 c97 c104 c108 c119
  rcases group31 with ⟨h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44⟩
  have group45 := chunk3 a start36 h43 h36 h33 start59 h38 start4 h17 c20 c122 c162 c176
  rcases group45 with ⟨h46,h47,h48,h49⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h2) (And.intro (forced (a 3) 0 h6) (And.intro (forced (a 4) 0 h49) (And.intro (forced (a 5) 0 start5) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 h3) (And.intro (forced (a 8) 0 h13) (And.intro (forced (a 9) 0 h7) (And.intro (forced (a 10) 0 h10) (And.intro (forced (a 11) 0 start11) (And.intro (forced (a 12) 0 h17) (And.intro (forced (a 13) 0 h20) (And.intro (forced (a 14) 0 start14) (And.intro (forced (a 15) 0 h4) (And.intro (forced (a 16) 0 h27) (And.intro (forced (a 17) 0 h8) (And.intro (forced (a 18) 0 h11) (And.intro (forced (a 19) 0 h28) (And.intro (forced (a 20) 0 h30) (And.intro (forced (a 21) 0 start21) (And.intro (forced (a 22) 0 h34) (And.intro (forced (a 23) 0 h14) (And.intro (forced (a 24) 0 h18) (And.intro (forced (a 25) 0 h21) (And.intro (forced (a 26) 0 h23) (And.intro (forced (a 27) 0 start27) (And.intro (forced (a 28) 0 start28) (And.intro (forced (a 29) 0 h26) (And.intro (forced (a 30) 0 start30) (And.intro (forced (a 31) 0 h5) (And.intro (forced (a 32) 0 start32) (And.intro (forced (a 33) 0 h9) (And.intro (forced (a 34) 0 h12) (And.intro (forced (a 35) 0 h43) (And.intro (forced (a 36) 0 h46) (And.intro (forced (a 37) 0 start37) (And.intro (forced (a 38) 0 h44) (And.intro (forced (a 39) 0 h15) (And.intro (forced (a 40) 0 h19) (And.intro (forced (a 41) 0 h22) (And.intro (forced (a 42) 0 h24) (And.intro (forced (a 43) 0 start43) (And.intro (forced (a 44) 0 h25) (And.intro (forced (a 45) 0 start45) (And.intro (forced (a 46) 0 start46) (And.intro (forced (a 47) 0 h29) (And.intro (forced (a 48) 0 h32) (And.intro (forced (a 49) 0 h33) (And.intro (forced (a 50) 0 h35) (And.intro (forced (a 51) 0 start51) (And.intro (forced (a 52) 0 start52) (And.intro (forced (a 53) 0 h47) (And.intro (forced (a 54) 0 h37) (And.intro (forced (a 55) 0 h38) (And.intro (forced (a 56) 0 h39) (And.intro (forced (a 57) 0 h40) (And.intro (forced (a 58) 0 h41) (And.intro (forced (a 59) 0 h48) (And.intro (forced (a 60) 0 start60) (And.intro (forced (a 61) 0 h42) (forced (a 62) 0 start62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_243
