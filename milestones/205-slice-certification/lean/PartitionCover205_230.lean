import FiniteDomain205
namespace PartitionCover205_230
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[1]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[3]
def r5 : Array Nat := #[3]
def r6 : Array Nat := #[3]
def r7 : Array Nat := #[3]
def r8 : Array Nat := #[3]
def r9 : Array Nat := #[3]
def r10 : Array Nat := #[3]
def r11 : Array Nat := #[3]
def r12 : Array Nat := #[1]
def r13 : Array Nat := #[3]
def r14 : Array Nat := #[3]
def r15 : Array Nat := #[3]
def r16 : Array Nat := #[1,2]
def r17 : Array Nat := #[1,1]
def r18 : Array Nat := #[1,1]
def r19 : Array Nat := #[1,1]
def r20 : Array Nat := #[1,2]
def r21 : Array Nat := #[1,1]
def r22 : Array Nat := #[1,2]
def r23 : Array Nat := #[1,1]
def r24 : Array Nat := #[1,1]
def r25 : Array Nat := #[1,2]
def r26 : Array Nat := #[1,1]
def r27 : Array Nat := #[1,1]
def r28 : Array Nat := #[3]
def r29 : Array Nat := #[3]
def r30 : Array Nat := #[3]
def r31 : Array Nat := #[1]
def r32 : Array Nat := #[1,2]
def r33 : Array Nat := #[1,1]
def r34 : Array Nat := #[1,1]
def r35 : Array Nat := #[3]
def r36 : Array Nat := #[3]
def r37 : Array Nat := #[3]
def r38 : Array Nat := #[1]
def r39 : Array Nat := #[1,1]
def r40 : Array Nat := #[1,2]
def r41 : Array Nat := #[1,2]
def r42 : Array Nat := #[1,1]
def r43 : Array Nat := #[1,2]
def r44 : Array Nat := #[1,1]
def r45 : Array Nat := #[1,2]
def r46 : Array Nat := #[3]
def r47 : Array Nat := #[1]
def r48 : Array Nat := #[1]
def r49 : Array Nat := #[1,2]
def r50 : Array Nat := #[1,1]
def r51 : Array Nat := #[1,2]
def r52 : Array Nat := #[1,2]
def r53 : Array Nat := #[1,2]
def r54 : Array Nat := #[1,2]
def r55 : Array Nat := #[1,2]
def r56 : Array Nat := #[1,2]
def r57 : Array Nat := #[1,2]
def r58 : Array Nat := #[1,1]
def r59 : Array Nat := #[1,1]
def r60 : Array Nat := #[1,1]
def r61 : Array Nat := #[1,1]
def r62 : Array Nat := #[1,1]
def r63 : Array Nat := #[1,2]
def r64 : Array Nat := #[1,1]
def r65 : Array Nat := #[1,1]
def r66 : Array Nat := #[1,2]
def r67 : Array Nat := #[1,1]
def r68 : Array Nat := #[1,1]
def r69 : Array Nat := #[1]
def r70 : Array Nat := #[1]
def r71 : Array Nat := #[3]
def r72 : Array Nat := #[1]
def r73 : Array Nat := #[3]
def r74 : Array Nat := #[1]
def r75 : Array Nat := #[3]
def r76 : Array Nat := #[1]
def r77 : Array Nat := #[3]
def r78 : Array Nat := #[1,1]
def r79 : Array Nat := #[1,2]
def r80 : Array Nat := #[1,1]
def r81 : Array Nat := #[3]
def r82 : Array Nat := #[3]
def r83 : Array Nat := #[3]
def r84 : Array Nat := #[1]
def r85 : Array Nat := #[1]
def r86 : Array Nat := #[3]
def r87 : Array Nat := #[1,1]
def r88 : Array Nat := #[1,1]
def r89 : Array Nat := #[1]
def r90 : Array Nat := #[3]
def r91 : Array Nat := #[3]
def r92 : Array Nat := #[3]
def r93 : Array Nat := #[3]
def r94 : Array Nat := #[3]
def r95 : Array Nat := #[3]
def r96 : Array Nat := #[1,2]
def r97 : Array Nat := #[1,2]
def r98 : Array Nat := #[1,2]
def r99 : Array Nat := #[1,2]
def r100 : Array Nat := #[1,2]
def r101 : Array Nat := #[1,1]
def r102 : Array Nat := #[1,1]
def r103 : Array Nat := #[1,1]
def r104 : Array Nat := #[1,1]
def r105 : Array Nat := #[1,2]
def r106 : Array Nat := #[1,1]
def r107 : Array Nat := #[1,1]
def r108 : Array Nat := #[1,1]
def r109 : Array Nat := #[1,2]
def r110 : Array Nat := #[1,1]
def r111 : Array Nat := #[1]
def r112 : Array Nat := #[1]
def r113 : Array Nat := #[3]
def r114 : Array Nat := #[1]
def r115 : Array Nat := #[1]
def r116 : Array Nat := #[3]
def r117 : Array Nat := #[3]
def r118 : Array Nat := #[1]
def r119 : Array Nat := #[1]
def r120 : Array Nat := #[3]
def r121 : Array Nat := #[1]
def r122 : Array Nat := #[1]
def r123 : Array Nat := #[3]
def r124 : Array Nat := #[3]
def r125 : Array Nat := #[1,1]
def r126 : Array Nat := #[1,1]
def r127 : Array Nat := #[1,1]
def r128 : Array Nat := #[1,1]
def r129 : Array Nat := #[1,2]
def r130 : Array Nat := #[3]
def r131 : Array Nat := #[3]
def r132 : Array Nat := #[1,1]
def r133 : Array Nat := #[1,2]
def r134 : Array Nat := #[3]
def r135 : Array Nat := #[3]
def r136 : Array Nat := #[1,2]
def r137 : Array Nat := #[1]
def r138 : Array Nat := #[1]
def r139 : Array Nat := #[3]
def r140 : Array Nat := #[3]
def r141 : Array Nat := #[3]
def r142 : Array Nat := #[3]
def r143 : Array Nat := #[1]
def r144 : Array Nat := #[3]
def r145 : Array Nat := #[1]
def r146 : Array Nat := #[3]
def r147 : Array Nat := #[1,2]
def r148 : Array Nat := #[1,2]
def r149 : Array Nat := #[1,2]
def r150 : Array Nat := #[1,1]
def r151 : Array Nat := #[1,2]
def r152 : Array Nat := #[1,2]
def r153 : Array Nat := #[1,2]
def r154 : Array Nat := #[3]
def r155 : Array Nat := #[3]
def r156 : Array Nat := #[1,2]
def r157 : Array Nat := #[1,1]
def r158 : Array Nat := #[1,2]
def r159 : Array Nat := #[1,2]
def r160 : Array Nat := #[3]
def r161 : Array Nat := #[3]
def r162 : Array Nat := #[1,2]
def r163 : Array Nat := #[1,2]
def r164 : Array Nat := #[1,2]
def r165 : Array Nat := #[1,2]
def r166 : Array Nat := #[1,2]
def r167 : Array Nat := #[1,2]
def r168 : Array Nat := #[1,2]
theorem chunk0 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d58 : a 58 ∈ [0,1])
    (d59 : a 59 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d54 : a 54 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (c16 : edge r16 (a 3) (a 7)=true)
    (c20 : edge r20 (a 4) (a 5)=true)
    (c25 : edge r25 (a 5) (a 7)=true)
    (c32 : edge r32 (a 7) (a 14)=true)
    (c52 : edge r52 (a 13) (a 14)=true)
    (c53 : edge r53 (a 13) (a 28)=true)
    (c54 : edge r54 (a 14) (a 29)=true)
    (c55 : edge r55 (a 14) (a 43)=true)
    (c79 : edge r79 (a 21) (a 28)=true)
    (c97 : edge r97 (a 28) (a 58)=true)
    (c98 : edge r98 (a 29) (a 59)=true)
    (c156 : edge r156 (a 51) (a 59)=true)
    (c163 : edge r163 (a 54) (a 58)=true)
    (c164 : edge r164 (a 55) (a 59)=true)
    (c166 : edge r166 (a 56) (a 58)=true)
    (c167 : edge r167 (a 57) (a 59)=true)
    : a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 14 ∈ [0] ∧ a 13 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 43 ∈ [0] ∧ a 21 ∈ [0] ∧ a 58 ∈ [0] ∧ a 59 ∈ [0] ∧ a 51 ∈ [0] ∧ a 54 ∈ [0] ∧ a 55 ∈ [0] ∧ a 56 ∈ [0] ∧ a 57 ∈ [0] ∧ a 4 ∈ [0] := by
  have b0 : a 7 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 7) (a 3) 1 d3 c16 (by decide +kernel)
  have t0 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b0
  have b1 : a 5 ≠ 1 := exclude [0] (edge r25) (a 5) (a 7) 1 t0 c25 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 14 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 14) (a 7) 1 t0 c32 (by decide +kernel)
  have t2 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b2
  have b3 : a 13 ≠ 1 := exclude [0] (edge r52) (a 13) (a 14) 1 t2 c52 (by decide +kernel)
  have t3 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b3
  have b4 : a 28 ≠ 1 := exclude [0] (fun u v => edge r53 v u) (a 28) (a 13) 1 t3 c53 (by decide +kernel)
  have t4 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b4
  have b5 : a 29 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 29) (a 14) 1 t2 c54 (by decide +kernel)
  have t5 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b5
  have b6 : a 43 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 43) (a 14) 1 t2 c55 (by decide +kernel)
  have t6 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b6
  have b7 : a 21 ≠ 1 := exclude [0] (edge r79) (a 21) (a 28) 1 t4 c79 (by decide +kernel)
  have t7 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b7
  have b8 : a 58 ≠ 1 := exclude [0] (fun u v => edge r97 v u) (a 58) (a 28) 1 t4 c97 (by decide +kernel)
  have t8 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b8
  have b9 : a 59 ≠ 1 := exclude [0] (fun u v => edge r98 v u) (a 59) (a 29) 1 t5 c98 (by decide +kernel)
  have t9 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b9
  have b10 : a 51 ≠ 1 := exclude [0] (edge r156) (a 51) (a 59) 1 t9 c156 (by decide +kernel)
  have t10 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b10
  have b11 : a 54 ≠ 1 := exclude [0] (edge r163) (a 54) (a 58) 1 t8 c163 (by decide +kernel)
  have t11 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b11
  have b12 : a 55 ≠ 1 := exclude [0] (edge r164) (a 55) (a 59) 1 t9 c164 (by decide +kernel)
  have t12 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b12
  have b13 : a 56 ≠ 1 := exclude [0] (edge r166) (a 56) (a 58) 1 t8 c166 (by decide +kernel)
  have t13 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b13
  have b14 : a 57 ≠ 1 := exclude [0] (edge r167) (a 57) (a 59) 1 t9 c167 (by decide +kernel)
  have t14 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b14
  have b15 : a 4 ≠ 1 := exclude [0] (edge r20) (a 4) (a 5) 1 t1 c20 (by decide +kernel)
  have t15 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk1 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d32 : a 32 ∈ [0,1])
    (d47 : a 47 ∈ [0,1])
    (d51 : a 51 ∈ [0])
    (d48 : a 48 ∈ [0,1])
    (d56 : a 56 ∈ [0])
    (d49 : a 49 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d54 : a 54 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (c22 : edge r22 (a 4) (a 12)=true)
    (c43 : edge r43 (a 10) (a 13)=true)
    (c45 : edge r45 (a 10) (a 39)=true)
    (c51 : edge r51 (a 12) (a 41)=true)
    (c56 : edge r56 (a 15) (a 16)=true)
    (c57 : edge r57 (a 15) (a 17)=true)
    (c63 : edge r63 (a 16) (a 24)=true)
    (c66 : edge r66 (a 17) (a 21)=true)
    (c99 : edge r99 (a 30) (a 31)=true)
    (c100 : edge r100 (a 30) (a 32)=true)
    (c105 : edge r105 (a 31) (a 38)=true)
    (c109 : edge r109 (a 32) (a 39)=true)
    (c147 : edge r147 (a 47) (a 51)=true)
    (c151 : edge r151 (a 48) (a 56)=true)
    (c152 : edge r152 (a 49) (a 51)=true)
    (c158 : edge r158 (a 52) (a 54)=true)
    : a 12 ∈ [0] ∧ a 10 ∈ [0] ∧ a 39 ∈ [0] ∧ a 41 ∈ [0] ∧ a 17 ∈ [0] ∧ a 32 ∈ [0] ∧ a 47 ∈ [0] ∧ a 48 ∈ [0] ∧ a 49 ∈ [0] ∧ a 52 ∈ [0] ∧ a 15 ∈ [0] ∧ a 30 ∈ [0] ∧ a 16 ∈ [0] ∧ a 24 ∈ [0] ∧ a 31 ∈ [0] ∧ a 38 ∈ [0] := by
  have b0 : a 12 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 4) 1 d4 c22 (by decide +kernel)
  have t0 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b0
  have b1 : a 10 ≠ 1 := exclude [0] (edge r43) (a 10) (a 13) 1 d13 c43 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b1
  have b2 : a 39 ≠ 1 := exclude [0] (fun u v => edge r45 v u) (a 39) (a 10) 1 t1 c45 (by decide +kernel)
  have t2 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b2
  have b3 : a 41 ≠ 1 := exclude [0] (fun u v => edge r51 v u) (a 41) (a 12) 1 t0 c51 (by decide +kernel)
  have t3 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b3
  have b4 : a 17 ≠ 1 := exclude [0] (edge r66) (a 17) (a 21) 1 d21 c66 (by decide +kernel)
  have t4 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b4
  have b5 : a 32 ≠ 1 := exclude [0] (edge r109) (a 32) (a 39) 1 t2 c109 (by decide +kernel)
  have t5 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b5
  have b6 : a 47 ≠ 1 := exclude [0] (edge r147) (a 47) (a 51) 1 d51 c147 (by decide +kernel)
  have t6 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b6
  have b7 : a 48 ≠ 1 := exclude [0] (edge r151) (a 48) (a 56) 1 d56 c151 (by decide +kernel)
  have t7 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b7
  have b8 : a 49 ≠ 1 := exclude [0] (edge r152) (a 49) (a 51) 1 d51 c152 (by decide +kernel)
  have t8 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b8
  have b9 : a 52 ≠ 1 := exclude [0] (edge r158) (a 52) (a 54) 1 d54 c158 (by decide +kernel)
  have t9 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b9
  have b10 : a 15 ≠ 1 := exclude [0] (edge r57) (a 15) (a 17) 1 t4 c57 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b10
  have b11 : a 30 ≠ 1 := exclude [0] (edge r100) (a 30) (a 32) 1 t5 c100 (by decide +kernel)
  have t11 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b11
  have b12 : a 16 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 16) (a 15) 1 t10 c56 (by decide +kernel)
  have t12 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b12
  have b13 : a 24 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 24) (a 16) 1 t12 c63 (by decide +kernel)
  have t13 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b13
  have b14 : a 31 ≠ 1 := exclude [0] (fun u v => edge r99 v u) (a 31) (a 30) 1 t11 c99 (by decide +kernel)
  have t14 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b14
  have b15 : a 38 ≠ 1 := exclude [0] (fun u v => edge r105 v u) (a 38) (a 31) 1 t14 c105 (by decide +kernel)
  have t15 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk2 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (c40 : edge r40 (a 9) (a 24)=true)
    : a 9 ∈ [0] := by
  have b0 : a 9 ≠ 1 := exclude [0] (edge r40) (a 9) (a 24) 1 d24 c40 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b0
  exact t0

theorem chunk3 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1])
    (d3 : a 3 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d58 : a 58 ∈ [0,1])
    (d59 : a 59 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d54 : a 54 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (c16 : edge r16 (a 3) (a 7)=true)
    (c20 : edge r20 (a 4) (a 5)=true)
    (c25 : edge r25 (a 5) (a 7)=true)
    (c32 : edge r32 (a 7) (a 14)=true)
    (c52 : edge r52 (a 13) (a 14)=true)
    (c53 : edge r53 (a 13) (a 28)=true)
    (c54 : edge r54 (a 14) (a 29)=true)
    (c55 : edge r55 (a 14) (a 43)=true)
    (c79 : edge r79 (a 21) (a 28)=true)
    (c97 : edge r97 (a 28) (a 58)=true)
    (c98 : edge r98 (a 29) (a 59)=true)
    (c156 : edge r156 (a 51) (a 59)=true)
    (c163 : edge r163 (a 54) (a 58)=true)
    (c164 : edge r164 (a 55) (a 59)=true)
    (c166 : edge r166 (a 56) (a 58)=true)
    (c167 : edge r167 (a 57) (a 59)=true)
    : a 7 ∈ [1] ∧ a 5 ∈ [1] ∧ a 14 ∈ [1] ∧ a 13 ∈ [1] ∧ a 28 ∈ [1] ∧ a 29 ∈ [1] ∧ a 43 ∈ [1] ∧ a 21 ∈ [1] ∧ a 58 ∈ [1] ∧ a 59 ∈ [1] ∧ a 51 ∈ [1] ∧ a 54 ∈ [1] ∧ a 55 ∈ [1] ∧ a 56 ∈ [1] ∧ a 57 ∈ [1] ∧ a 4 ∈ [1] := by
  have b0 : a 7 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 7) (a 3) 0 d3 c16 (by decide +kernel)
  have t0 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b0
  have b1 : a 5 ≠ 0 := exclude [1] (edge r25) (a 5) (a 7) 0 t0 c25 (by decide +kernel)
  have t1 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b1
  have b2 : a 14 ≠ 0 := exclude [1] (fun u v => edge r32 v u) (a 14) (a 7) 0 t0 c32 (by decide +kernel)
  have t2 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b2
  have b3 : a 13 ≠ 0 := exclude [1] (edge r52) (a 13) (a 14) 0 t2 c52 (by decide +kernel)
  have t3 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b3
  have b4 : a 28 ≠ 0 := exclude [1] (fun u v => edge r53 v u) (a 28) (a 13) 0 t3 c53 (by decide +kernel)
  have t4 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b4
  have b5 : a 29 ≠ 0 := exclude [1] (fun u v => edge r54 v u) (a 29) (a 14) 0 t2 c54 (by decide +kernel)
  have t5 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b5
  have b6 : a 43 ≠ 0 := exclude [1] (fun u v => edge r55 v u) (a 43) (a 14) 0 t2 c55 (by decide +kernel)
  have t6 : a 43 ∈ [1] := remove (a 43) 0 [0,1] d43 b6
  have b7 : a 21 ≠ 0 := exclude [1] (edge r79) (a 21) (a 28) 0 t4 c79 (by decide +kernel)
  have t7 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b7
  have b8 : a 58 ≠ 0 := exclude [1] (fun u v => edge r97 v u) (a 58) (a 28) 0 t4 c97 (by decide +kernel)
  have t8 : a 58 ∈ [1] := remove (a 58) 0 [0,1] d58 b8
  have b9 : a 59 ≠ 0 := exclude [1] (fun u v => edge r98 v u) (a 59) (a 29) 0 t5 c98 (by decide +kernel)
  have t9 : a 59 ∈ [1] := remove (a 59) 0 [0,1] d59 b9
  have b10 : a 51 ≠ 0 := exclude [1] (edge r156) (a 51) (a 59) 0 t9 c156 (by decide +kernel)
  have t10 : a 51 ∈ [1] := remove (a 51) 0 [0,1] d51 b10
  have b11 : a 54 ≠ 0 := exclude [1] (edge r163) (a 54) (a 58) 0 t8 c163 (by decide +kernel)
  have t11 : a 54 ∈ [1] := remove (a 54) 0 [0,1] d54 b11
  have b12 : a 55 ≠ 0 := exclude [1] (edge r164) (a 55) (a 59) 0 t9 c164 (by decide +kernel)
  have t12 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b12
  have b13 : a 56 ≠ 0 := exclude [1] (edge r166) (a 56) (a 58) 0 t8 c166 (by decide +kernel)
  have t13 : a 56 ∈ [1] := remove (a 56) 0 [0,1] d56 b13
  have b14 : a 57 ≠ 0 := exclude [1] (edge r167) (a 57) (a 59) 0 t9 c167 (by decide +kernel)
  have t14 : a 57 ∈ [1] := remove (a 57) 0 [0,1] d57 b14
  have b15 : a 4 ≠ 0 := exclude [1] (edge r20) (a 4) (a 5) 0 t1 c20 (by decide +kernel)
  have t15 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk4 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1])
    (d4 : a 4 ∈ [1])
    (d10 : a 10 ∈ [0,1])
    (d13 : a 13 ∈ [1])
    (d39 : a 39 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [1])
    (d32 : a 32 ∈ [0,1])
    (d47 : a 47 ∈ [0,1])
    (d51 : a 51 ∈ [1])
    (d48 : a 48 ∈ [0,1])
    (d56 : a 56 ∈ [1])
    (d49 : a 49 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d54 : a 54 ∈ [1])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (c22 : edge r22 (a 4) (a 12)=true)
    (c43 : edge r43 (a 10) (a 13)=true)
    (c45 : edge r45 (a 10) (a 39)=true)
    (c51 : edge r51 (a 12) (a 41)=true)
    (c56 : edge r56 (a 15) (a 16)=true)
    (c57 : edge r57 (a 15) (a 17)=true)
    (c63 : edge r63 (a 16) (a 24)=true)
    (c66 : edge r66 (a 17) (a 21)=true)
    (c99 : edge r99 (a 30) (a 31)=true)
    (c100 : edge r100 (a 30) (a 32)=true)
    (c105 : edge r105 (a 31) (a 38)=true)
    (c109 : edge r109 (a 32) (a 39)=true)
    (c147 : edge r147 (a 47) (a 51)=true)
    (c151 : edge r151 (a 48) (a 56)=true)
    (c152 : edge r152 (a 49) (a 51)=true)
    (c158 : edge r158 (a 52) (a 54)=true)
    : a 12 ∈ [1] ∧ a 10 ∈ [1] ∧ a 39 ∈ [1] ∧ a 41 ∈ [1] ∧ a 17 ∈ [1] ∧ a 32 ∈ [1] ∧ a 47 ∈ [1] ∧ a 48 ∈ [1] ∧ a 49 ∈ [1] ∧ a 52 ∈ [1] ∧ a 15 ∈ [1] ∧ a 30 ∈ [1] ∧ a 16 ∈ [1] ∧ a 24 ∈ [1] ∧ a 31 ∈ [1] ∧ a 38 ∈ [1] := by
  have b0 : a 12 ≠ 0 := exclude [1] (fun u v => edge r22 v u) (a 12) (a 4) 0 d4 c22 (by decide +kernel)
  have t0 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b0
  have b1 : a 10 ≠ 0 := exclude [1] (edge r43) (a 10) (a 13) 0 d13 c43 (by decide +kernel)
  have t1 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b1
  have b2 : a 39 ≠ 0 := exclude [1] (fun u v => edge r45 v u) (a 39) (a 10) 0 t1 c45 (by decide +kernel)
  have t2 : a 39 ∈ [1] := remove (a 39) 0 [0,1] d39 b2
  have b3 : a 41 ≠ 0 := exclude [1] (fun u v => edge r51 v u) (a 41) (a 12) 0 t0 c51 (by decide +kernel)
  have t3 : a 41 ∈ [1] := remove (a 41) 0 [0,1] d41 b3
  have b4 : a 17 ≠ 0 := exclude [1] (edge r66) (a 17) (a 21) 0 d21 c66 (by decide +kernel)
  have t4 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b4
  have b5 : a 32 ≠ 0 := exclude [1] (edge r109) (a 32) (a 39) 0 t2 c109 (by decide +kernel)
  have t5 : a 32 ∈ [1] := remove (a 32) 0 [0,1] d32 b5
  have b6 : a 47 ≠ 0 := exclude [1] (edge r147) (a 47) (a 51) 0 d51 c147 (by decide +kernel)
  have t6 : a 47 ∈ [1] := remove (a 47) 0 [0,1] d47 b6
  have b7 : a 48 ≠ 0 := exclude [1] (edge r151) (a 48) (a 56) 0 d56 c151 (by decide +kernel)
  have t7 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b7
  have b8 : a 49 ≠ 0 := exclude [1] (edge r152) (a 49) (a 51) 0 d51 c152 (by decide +kernel)
  have t8 : a 49 ∈ [1] := remove (a 49) 0 [0,1] d49 b8
  have b9 : a 52 ≠ 0 := exclude [1] (edge r158) (a 52) (a 54) 0 d54 c158 (by decide +kernel)
  have t9 : a 52 ∈ [1] := remove (a 52) 0 [0,1] d52 b9
  have b10 : a 15 ≠ 0 := exclude [1] (edge r57) (a 15) (a 17) 0 t4 c57 (by decide +kernel)
  have t10 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b10
  have b11 : a 30 ≠ 0 := exclude [1] (edge r100) (a 30) (a 32) 0 t5 c100 (by decide +kernel)
  have t11 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b11
  have b12 : a 16 ≠ 0 := exclude [1] (fun u v => edge r56 v u) (a 16) (a 15) 0 t10 c56 (by decide +kernel)
  have t12 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b12
  have b13 : a 24 ≠ 0 := exclude [1] (fun u v => edge r63 v u) (a 24) (a 16) 0 t12 c63 (by decide +kernel)
  have t13 : a 24 ∈ [1] := remove (a 24) 0 [0,1] d24 b13
  have b14 : a 31 ≠ 0 := exclude [1] (fun u v => edge r99 v u) (a 31) (a 30) 0 t11 c99 (by decide +kernel)
  have t14 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b14
  have b15 : a 38 ≠ 0 := exclude [1] (fun u v => edge r105 v u) (a 38) (a 31) 0 t14 c105 (by decide +kernel)
  have t15 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d24 : a 24 ∈ [1])
    (c40 : edge r40 (a 9) (a 24)=true)
    : a 9 ∈ [1] := by
  have b0 : a 9 ≠ 0 := exclude [1] (edge r40) (a 9) (a 24) 0 d24 c40 (by decide +kernel)
  have t0 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b0
  exact t0
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0])
    (start3 : a 3 ∈ [0,1])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0])
    (start7 : a 7 ∈ [0,1])
    (start8 : a 8 ∈ [0])
    (start9 : a 9 ∈ [0,1])
    (start10 : a 10 ∈ [0,1])
    (start11 : a 11 ∈ [0])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1])
    (start14 : a 14 ∈ [0,1])
    (start15 : a 15 ∈ [0,1])
    (start16 : a 16 ∈ [0,1])
    (start17 : a 17 ∈ [0,1])
    (start18 : a 18 ∈ [0])
    (start19 : a 19 ∈ [0])
    (start20 : a 20 ∈ [0])
    (start21 : a 21 ∈ [0,1])
    (start22 : a 22 ∈ [0])
    (start23 : a 23 ∈ [0])
    (start24 : a 24 ∈ [0,1])
    (start25 : a 25 ∈ [0])
    (start26 : a 26 ∈ [0])
    (start27 : a 27 ∈ [0])
    (start28 : a 28 ∈ [0,1])
    (start29 : a 29 ∈ [0,1])
    (start30 : a 30 ∈ [0,1])
    (start31 : a 31 ∈ [0,1])
    (start32 : a 32 ∈ [0,1])
    (start33 : a 33 ∈ [0])
    (start34 : a 34 ∈ [0])
    (start35 : a 35 ∈ [0])
    (start36 : a 36 ∈ [0])
    (start37 : a 37 ∈ [0])
    (start38 : a 38 ∈ [0,1])
    (start39 : a 39 ∈ [0,1])
    (start40 : a 40 ∈ [0])
    (start41 : a 41 ∈ [0,1])
    (start42 : a 42 ∈ [0])
    (start43 : a 43 ∈ [0,1])
    (start44 : a 44 ∈ [0])
    (start45 : a 45 ∈ [0])
    (start46 : a 46 ∈ [0])
    (start47 : a 47 ∈ [0,1])
    (start48 : a 48 ∈ [0,1])
    (start49 : a 49 ∈ [0,1])
    (start50 : a 50 ∈ [0])
    (start51 : a 51 ∈ [0,1])
    (start52 : a 52 ∈ [0,1])
    (start53 : a 53 ∈ [0])
    (start54 : a 54 ∈ [0,1])
    (start55 : a 55 ∈ [0,1])
    (start56 : a 56 ∈ [0,1])
    (start57 : a 57 ∈ [0,1])
    (start58 : a 58 ∈ [0,1])
    (start59 : a 59 ∈ [0,1])
    (c0 : edge r0 (a 0) (a 1)=true)
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 15)=true)
    (c5 : edge r5 (a 0) (a 30)=true)
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 9)=true)
    (c9 : edge r9 (a 1) (a 16)=true)
    (c10 : edge r10 (a 1) (a 31)=true)
    (c11 : edge r11 (a 2) (a 3)=true)
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 17)=true)
    (c15 : edge r15 (a 2) (a 32)=true)
    (c16 : edge r16 (a 3) (a 7)=true)
    (c17 : edge r17 (a 3) (a 11)=true)
    (c18 : edge r18 (a 3) (a 18)=true)
    (c19 : edge r19 (a 3) (a 33)=true)
    (c20 : edge r20 (a 4) (a 5)=true)
    (c21 : edge r21 (a 4) (a 6)=true)
    (c22 : edge r22 (a 4) (a 12)=true)
    (c23 : edge r23 (a 4) (a 19)=true)
    (c24 : edge r24 (a 4) (a 34)=true)
    (c25 : edge r25 (a 5) (a 7)=true)
    (c26 : edge r26 (a 5) (a 20)=true)
    (c27 : edge r27 (a 5) (a 35)=true)
    (c28 : edge r28 (a 6) (a 7)=true)
    (c29 : edge r29 (a 6) (a 13)=true)
    (c30 : edge r30 (a 6) (a 21)=true)
    (c31 : edge r31 (a 6) (a 36)=true)
    (c32 : edge r32 (a 7) (a 14)=true)
    (c33 : edge r33 (a 7) (a 22)=true)
    (c34 : edge r34 (a 7) (a 37)=true)
    (c35 : edge r35 (a 8) (a 9)=true)
    (c36 : edge r36 (a 8) (a 10)=true)
    (c37 : edge r37 (a 8) (a 12)=true)
    (c38 : edge r38 (a 8) (a 23)=true)
    (c39 : edge r39 (a 9) (a 11)=true)
    (c40 : edge r40 (a 9) (a 24)=true)
    (c41 : edge r41 (a 9) (a 38)=true)
    (c42 : edge r42 (a 10) (a 11)=true)
    (c43 : edge r43 (a 10) (a 13)=true)
    (c44 : edge r44 (a 10) (a 25)=true)
    (c45 : edge r45 (a 10) (a 39)=true)
    (c46 : edge r46 (a 11) (a 14)=true)
    (c47 : edge r47 (a 11) (a 26)=true)
    (c48 : edge r48 (a 11) (a 40)=true)
    (c49 : edge r49 (a 12) (a 13)=true)
    (c50 : edge r50 (a 12) (a 27)=true)
    (c51 : edge r51 (a 12) (a 41)=true)
    (c52 : edge r52 (a 13) (a 14)=true)
    (c53 : edge r53 (a 13) (a 28)=true)
    (c54 : edge r54 (a 14) (a 29)=true)
    (c55 : edge r55 (a 14) (a 43)=true)
    (c56 : edge r56 (a 15) (a 16)=true)
    (c57 : edge r57 (a 15) (a 17)=true)
    (c58 : edge r58 (a 15) (a 19)=true)
    (c59 : edge r59 (a 15) (a 23)=true)
    (c60 : edge r60 (a 15) (a 44)=true)
    (c61 : edge r61 (a 16) (a 18)=true)
    (c62 : edge r62 (a 16) (a 20)=true)
    (c63 : edge r63 (a 16) (a 24)=true)
    (c64 : edge r64 (a 16) (a 45)=true)
    (c65 : edge r65 (a 17) (a 18)=true)
    (c66 : edge r66 (a 17) (a 21)=true)
    (c67 : edge r67 (a 17) (a 25)=true)
    (c68 : edge r68 (a 17) (a 46)=true)
    (c69 : edge r69 (a 18) (a 22)=true)
    (c70 : edge r70 (a 18) (a 26)=true)
    (c71 : edge r71 (a 18) (a 47)=true)
    (c72 : edge r72 (a 19) (a 20)=true)
    (c73 : edge r73 (a 19) (a 21)=true)
    (c74 : edge r74 (a 19) (a 27)=true)
    (c75 : edge r75 (a 19) (a 48)=true)
    (c76 : edge r76 (a 20) (a 22)=true)
    (c77 : edge r77 (a 20) (a 49)=true)
    (c78 : edge r78 (a 21) (a 22)=true)
    (c79 : edge r79 (a 21) (a 28)=true)
    (c80 : edge r80 (a 21) (a 50)=true)
    (c81 : edge r81 (a 22) (a 29)=true)
    (c82 : edge r82 (a 22) (a 51)=true)
    (c83 : edge r83 (a 23) (a 24)=true)
    (c84 : edge r84 (a 23) (a 25)=true)
    (c85 : edge r85 (a 23) (a 27)=true)
    (c86 : edge r86 (a 23) (a 52)=true)
    (c87 : edge r87 (a 24) (a 26)=true)
    (c88 : edge r88 (a 24) (a 53)=true)
    (c89 : edge r89 (a 25) (a 26)=true)
    (c90 : edge r90 (a 25) (a 28)=true)
    (c91 : edge r91 (a 25) (a 54)=true)
    (c92 : edge r92 (a 26) (a 29)=true)
    (c93 : edge r93 (a 26) (a 55)=true)
    (c94 : edge r94 (a 27) (a 28)=true)
    (c95 : edge r95 (a 27) (a 56)=true)
    (c96 : edge r96 (a 28) (a 29)=true)
    (c97 : edge r97 (a 28) (a 58)=true)
    (c98 : edge r98 (a 29) (a 59)=true)
    (c99 : edge r99 (a 30) (a 31)=true)
    (c100 : edge r100 (a 30) (a 32)=true)
    (c101 : edge r101 (a 30) (a 34)=true)
    (c102 : edge r102 (a 30) (a 44)=true)
    (c103 : edge r103 (a 31) (a 33)=true)
    (c104 : edge r104 (a 31) (a 35)=true)
    (c105 : edge r105 (a 31) (a 38)=true)
    (c106 : edge r106 (a 31) (a 45)=true)
    (c107 : edge r107 (a 32) (a 33)=true)
    (c108 : edge r108 (a 32) (a 36)=true)
    (c109 : edge r109 (a 32) (a 39)=true)
    (c110 : edge r110 (a 32) (a 46)=true)
    (c111 : edge r111 (a 33) (a 37)=true)
    (c112 : edge r112 (a 33) (a 40)=true)
    (c113 : edge r113 (a 33) (a 47)=true)
    (c114 : edge r114 (a 34) (a 35)=true)
    (c115 : edge r115 (a 34) (a 36)=true)
    (c116 : edge r116 (a 34) (a 41)=true)
    (c117 : edge r117 (a 34) (a 48)=true)
    (c118 : edge r118 (a 35) (a 37)=true)
    (c119 : edge r119 (a 35) (a 42)=true)
    (c120 : edge r120 (a 35) (a 49)=true)
    (c121 : edge r121 (a 36) (a 37)=true)
    (c122 : edge r122 (a 36) (a 50)=true)
    (c123 : edge r123 (a 37) (a 43)=true)
    (c124 : edge r124 (a 37) (a 51)=true)
    (c125 : edge r125 (a 38) (a 40)=true)
    (c126 : edge r126 (a 38) (a 42)=true)
    (c127 : edge r127 (a 38) (a 53)=true)
    (c128 : edge r128 (a 39) (a 40)=true)
    (c129 : edge r129 (a 39) (a 54)=true)
    (c130 : edge r130 (a 40) (a 43)=true)
    (c131 : edge r131 (a 40) (a 55)=true)
    (c132 : edge r132 (a 41) (a 42)=true)
    (c133 : edge r133 (a 41) (a 56)=true)
    (c134 : edge r134 (a 42) (a 43)=true)
    (c135 : edge r135 (a 42) (a 57)=true)
    (c136 : edge r136 (a 43) (a 59)=true)
    (c137 : edge r137 (a 44) (a 45)=true)
    (c138 : edge r138 (a 44) (a 46)=true)
    (c139 : edge r139 (a 44) (a 48)=true)
    (c140 : edge r140 (a 44) (a 52)=true)
    (c141 : edge r141 (a 45) (a 47)=true)
    (c142 : edge r142 (a 45) (a 49)=true)
    (c143 : edge r143 (a 45) (a 53)=true)
    (c144 : edge r144 (a 46) (a 47)=true)
    (c145 : edge r145 (a 46) (a 50)=true)
    (c146 : edge r146 (a 46) (a 54)=true)
    (c147 : edge r147 (a 47) (a 51)=true)
    (c148 : edge r148 (a 47) (a 55)=true)
    (c149 : edge r149 (a 48) (a 49)=true)
    (c150 : edge r150 (a 48) (a 50)=true)
    (c151 : edge r151 (a 48) (a 56)=true)
    (c152 : edge r152 (a 49) (a 51)=true)
    (c153 : edge r153 (a 49) (a 57)=true)
    (c154 : edge r154 (a 50) (a 51)=true)
    (c155 : edge r155 (a 50) (a 58)=true)
    (c156 : edge r156 (a 51) (a 59)=true)
    (c157 : edge r157 (a 52) (a 53)=true)
    (c158 : edge r158 (a 52) (a 54)=true)
    (c159 : edge r159 (a 52) (a 56)=true)
    (c160 : edge r160 (a 53) (a 55)=true)
    (c161 : edge r161 (a 53) (a 57)=true)
    (c162 : edge r162 (a 54) (a 55)=true)
    (c163 : edge r163 (a 54) (a 58)=true)
    (c164 : edge r164 (a 55) (a 59)=true)
    (c165 : edge r165 (a 56) (a 57)=true)
    (c166 : edge r166 (a 56) (a 58)=true)
    (c167 : edge r167 (a 57) (a 59)=true)
    (c168 : edge r168 (a 58) (a 59)=true)
    : (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=0 ∧ a 4=0 ∧ a 5=0 ∧ a 6=0 ∧ a 7=0 ∧ a 8=0 ∧ a 9=0 ∧ a 10=0 ∧ a 11=0 ∧ a 12=0 ∧ a 13=0 ∧ a 14=0 ∧ a 15=0 ∧ a 16=0 ∧ a 17=0 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=0 ∧ a 22=0 ∧ a 23=0 ∧ a 24=0 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=0 ∧ a 29=0 ∧ a 30=0 ∧ a 31=0 ∧ a 32=0 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=0 ∧ a 37=0 ∧ a 38=0 ∧ a 39=0 ∧ a 40=0 ∧ a 41=0 ∧ a 42=0 ∧ a 43=0 ∧ a 44=0 ∧ a 45=0 ∧ a 46=0 ∧ a 47=0 ∧ a 48=0 ∧ a 49=0 ∧ a 50=0 ∧ a 51=0 ∧ a 52=0 ∧ a 53=0 ∧ a 54=0 ∧ a 55=0 ∧ a 56=0 ∧ a 57=0 ∧ a 58=0 ∧ a 59=0) ∨
      (a 0=0 ∧ a 1=0 ∧ a 2=0 ∧ a 3=1 ∧ a 4=1 ∧ a 5=1 ∧ a 6=0 ∧ a 7=1 ∧ a 8=0 ∧ a 9=1 ∧ a 10=1 ∧ a 11=0 ∧ a 12=1 ∧ a 13=1 ∧ a 14=1 ∧ a 15=1 ∧ a 16=1 ∧ a 17=1 ∧ a 18=0 ∧ a 19=0 ∧ a 20=0 ∧ a 21=1 ∧ a 22=0 ∧ a 23=0 ∧ a 24=1 ∧ a 25=0 ∧ a 26=0 ∧ a 27=0 ∧ a 28=1 ∧ a 29=1 ∧ a 30=1 ∧ a 31=1 ∧ a 32=1 ∧ a 33=0 ∧ a 34=0 ∧ a 35=0 ∧ a 36=0 ∧ a 37=0 ∧ a 38=1 ∧ a 39=1 ∧ a 40=0 ∧ a 41=1 ∧ a 42=0 ∧ a 43=1 ∧ a 44=0 ∧ a 45=0 ∧ a 46=0 ∧ a 47=1 ∧ a 48=1 ∧ a 49=1 ∧ a 50=0 ∧ a 51=1 ∧ a 52=1 ∧ a 53=0 ∧ a 54=1 ∧ a 55=1 ∧ a 56=1 ∧ a 57=1 ∧ a 58=1 ∧ a 59=1) := by
  rcases (show a 3=0 ∨ a 3=1 from by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using start3) with q1 | q2
  · have h3 : a 3 ∈ [0] := List.mem_singleton.mpr q1
    have group4 := chunk0 a start7 h3 start5 start14 start13 start28 start29 start43 start21 start58 start59 start51 start54 start55 start56 start57 start4 c16 c20 c25 c32 c52 c53 c54 c55 c79 c97 c98 c156 c163 c164 c166 c167
    rcases group4 with ⟨h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20⟩
    have group21 := chunk1 a start12 h20 start10 h8 start39 start41 start17 h12 start32 start47 h15 start48 h18 start49 start52 h16 start15 start30 start16 start24 start31 start38 c22 c43 c45 c51 c56 c57 c63 c66 c99 c100 c105 c109 c147 c151 c152 c158
    rcases group21 with ⟨h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37⟩
    have group38 := chunk2 a start9 h35 c40
    have h39 := group38
    exact Or.inl (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 0 h3) (And.intro (forced (a 4) 0 h20) (And.intro (forced (a 5) 0 h6) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 0 h5) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 0 h39) (And.intro (forced (a 10) 0 h23) (And.intro (forced (a 11) 0 start11) (And.intro (forced (a 12) 0 h22) (And.intro (forced (a 13) 0 h8) (And.intro (forced (a 14) 0 h7) (And.intro (forced (a 15) 0 h32) (And.intro (forced (a 16) 0 h34) (And.intro (forced (a 17) 0 h26) (And.intro (forced (a 18) 0 start18) (And.intro (forced (a 19) 0 start19) (And.intro (forced (a 20) 0 start20) (And.intro (forced (a 21) 0 h12) (And.intro (forced (a 22) 0 start22) (And.intro (forced (a 23) 0 start23) (And.intro (forced (a 24) 0 h35) (And.intro (forced (a 25) 0 start25) (And.intro (forced (a 26) 0 start26) (And.intro (forced (a 27) 0 start27) (And.intro (forced (a 28) 0 h9) (And.intro (forced (a 29) 0 h10) (And.intro (forced (a 30) 0 h33) (And.intro (forced (a 31) 0 h36) (And.intro (forced (a 32) 0 h27) (And.intro (forced (a 33) 0 start33) (And.intro (forced (a 34) 0 start34) (And.intro (forced (a 35) 0 start35) (And.intro (forced (a 36) 0 start36) (And.intro (forced (a 37) 0 start37) (And.intro (forced (a 38) 0 h37) (And.intro (forced (a 39) 0 h24) (And.intro (forced (a 40) 0 start40) (And.intro (forced (a 41) 0 h25) (And.intro (forced (a 42) 0 start42) (And.intro (forced (a 43) 0 h11) (And.intro (forced (a 44) 0 start44) (And.intro (forced (a 45) 0 start45) (And.intro (forced (a 46) 0 start46) (And.intro (forced (a 47) 0 h28) (And.intro (forced (a 48) 0 h29) (And.intro (forced (a 49) 0 h30) (And.intro (forced (a 50) 0 start50) (And.intro (forced (a 51) 0 h15) (And.intro (forced (a 52) 0 h31) (And.intro (forced (a 53) 0 start53) (And.intro (forced (a 54) 0 h16) (And.intro (forced (a 55) 0 h17) (And.intro (forced (a 56) 0 h18) (And.intro (forced (a 57) 0 h19) (And.intro (forced (a 58) 0 h13) (forced (a 59) 0 h14))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  · have h40 : a 3 ∈ [1] := List.mem_singleton.mpr q2
    have group41 := chunk3 a start7 h40 start5 start14 start13 start28 start29 start43 start21 start58 start59 start51 start54 start55 start56 start57 start4 c16 c20 c25 c32 c52 c53 c54 c55 c79 c97 c98 c156 c163 c164 c166 c167
    rcases group41 with ⟨h42,h43,h44,h45,h46,h47,h48,h49,h50,h51,h52,h53,h54,h55,h56,h57⟩
    have group58 := chunk4 a start12 h57 start10 h45 start39 start41 start17 h49 start32 start47 h52 start48 h55 start49 start52 h53 start15 start30 start16 start24 start31 start38 c22 c43 c45 c51 c56 c57 c63 c66 c99 c100 c105 c109 c147 c151 c152 c158
    rcases group58 with ⟨h59,h60,h61,h62,h63,h64,h65,h66,h67,h68,h69,h70,h71,h72,h73,h74⟩
    have group75 := chunk5 a start9 h72 c40
    have h76 := group75
    exact Or.inr (And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 start2) (And.intro (forced (a 3) 1 h40) (And.intro (forced (a 4) 1 h57) (And.intro (forced (a 5) 1 h43) (And.intro (forced (a 6) 0 start6) (And.intro (forced (a 7) 1 h42) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 1 h76) (And.intro (forced (a 10) 1 h60) (And.intro (forced (a 11) 0 start11) (And.intro (forced (a 12) 1 h59) (And.intro (forced (a 13) 1 h45) (And.intro (forced (a 14) 1 h44) (And.intro (forced (a 15) 1 h69) (And.intro (forced (a 16) 1 h71) (And.intro (forced (a 17) 1 h63) (And.intro (forced (a 18) 0 start18) (And.intro (forced (a 19) 0 start19) (And.intro (forced (a 20) 0 start20) (And.intro (forced (a 21) 1 h49) (And.intro (forced (a 22) 0 start22) (And.intro (forced (a 23) 0 start23) (And.intro (forced (a 24) 1 h72) (And.intro (forced (a 25) 0 start25) (And.intro (forced (a 26) 0 start26) (And.intro (forced (a 27) 0 start27) (And.intro (forced (a 28) 1 h46) (And.intro (forced (a 29) 1 h47) (And.intro (forced (a 30) 1 h70) (And.intro (forced (a 31) 1 h73) (And.intro (forced (a 32) 1 h64) (And.intro (forced (a 33) 0 start33) (And.intro (forced (a 34) 0 start34) (And.intro (forced (a 35) 0 start35) (And.intro (forced (a 36) 0 start36) (And.intro (forced (a 37) 0 start37) (And.intro (forced (a 38) 1 h74) (And.intro (forced (a 39) 1 h61) (And.intro (forced (a 40) 0 start40) (And.intro (forced (a 41) 1 h62) (And.intro (forced (a 42) 0 start42) (And.intro (forced (a 43) 1 h48) (And.intro (forced (a 44) 0 start44) (And.intro (forced (a 45) 0 start45) (And.intro (forced (a 46) 0 start46) (And.intro (forced (a 47) 1 h65) (And.intro (forced (a 48) 1 h66) (And.intro (forced (a 49) 1 h67) (And.intro (forced (a 50) 0 start50) (And.intro (forced (a 51) 1 h52) (And.intro (forced (a 52) 1 h68) (And.intro (forced (a 53) 0 start53) (And.intro (forced (a 54) 1 h53) (And.intro (forced (a 55) 1 h54) (And.intro (forced (a 56) 1 h55) (And.intro (forced (a 57) 1 h56) (And.intro (forced (a 58) 1 h50) (forced (a 59) 1 h51))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_230
