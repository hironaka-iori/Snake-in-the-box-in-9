import FiniteDomain205
namespace PartitionCover205_168
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def r0 : Array Nat := #[1]
def r1 : Array Nat := #[7]
def r2 : Array Nat := #[3]
def r3 : Array Nat := #[1]
def r4 : Array Nat := #[15]
def r5 : Array Nat := #[1]
def r6 : Array Nat := #[3]
def r7 : Array Nat := #[7]
def r8 : Array Nat := #[15]
def r9 : Array Nat := #[1,1,1]
def r10 : Array Nat := #[3,0,0]
def r11 : Array Nat := #[5,0,0]
def r12 : Array Nat := #[1,0,2]
def r13 : Array Nat := #[1]
def r14 : Array Nat := #[1]
def r15 : Array Nat := #[3]
def r16 : Array Nat := #[1,2]
def r17 : Array Nat := #[1,2]
def r18 : Array Nat := #[1,2]
def r19 : Array Nat := #[63,63]
def r20 : Array Nat := #[1,1]
def r21 : Array Nat := #[7,56]
def r22 : Array Nat := #[63,63]
def r23 : Array Nat := #[1,1]
def r24 : Array Nat := #[3,12]
def r25 : Array Nat := #[3,3]
def r26 : Array Nat := #[3]
def r27 : Array Nat := #[1]
def r28 : Array Nat := #[5]
def r29 : Array Nat := #[15]
def r30 : Array Nat := #[1]
def r31 : Array Nat := #[1]
def r32 : Array Nat := #[1,1,1]
def r33 : Array Nat := #[5,40,45]
def r34 : Array Nat := #[5,0,2]
def r35 : Array Nat := #[1,1,1,1]
def r36 : Array Nat := #[5,10,0,0]
def r37 : Array Nat := #[1,2,4,8]
def r38 : Array Nat := #[1]
def r39 : Array Nat := #[3]
def r40 : Array Nat := #[5,40]
def r41 : Array Nat := #[5,5]
def r42 : Array Nat := #[5,0]
def r43 : Array Nat := #[1,0,0,2,0,0]
def r44 : Array Nat := #[5,18,40,5,18,0]
def r45 : Array Nat := #[1,1,2,2]
def r46 : Array Nat := #[5,6,1,2]
def r47 : Array Nat := #[1,2]
def r48 : Array Nat := #[1,2,4,8]
def r49 : Array Nat := #[1,2,4,8]
def r50 : Array Nat := #[63,63,63,63]
def r51 : Array Nat := #[1,1,1,1]
def r52 : Array Nat := #[1,10,4,10]
def r53 : Array Nat := #[63,63,63,63]
def r54 : Array Nat := #[1,2,4,8]
def r55 : Array Nat := #[1,2,4,8]
def r56 : Array Nat := #[1,32,2,8]
def r57 : Array Nat := #[1,0,2,0]
def r58 : Array Nat := #[1,4,1,2]
def r59 : Array Nat := #[1,1,2,2]
def r60 : Array Nat := #[1,2,4,8,16,32]
def r61 : Array Nat := #[1,2,4,8,16,32]
def r62 : Array Nat := #[1,1,2,2,4,4]
def r63 : Array Nat := #[1,1,2,2,4,4]
def r64 : Array Nat := #[1,2,4,8,16,32]
def r65 : Array Nat := #[1,1,2,2,4,4]
def r66 : Array Nat := #[1,2,1,4,2,4]
def r67 : Array Nat := #[1,0,0]
def r68 : Array Nat := #[15]
def r69 : Array Nat := #[15]
def r70 : Array Nat := #[7]
def r71 : Array Nat := #[1,1,2,2]
def r72 : Array Nat := #[5,40,18,40]
def r73 : Array Nat := #[1,2,0,0]
def r74 : Array Nat := #[1,2,1,2]
def r75 : Array Nat := #[1,1]
def r76 : Array Nat := #[3,12,48]
def r77 : Array Nat := #[3,5,6]
def r78 : Array Nat := #[3,3,2,2,2,2]
def r79 : Array Nat := #[1,1,0]
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2])
    (d6 : a 6 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d23 : a 23 ∈ [0,1,2])
    (d7 : a 7 ∈ [0])
    (d9 : a 9 ∈ [0,1,2])
    (d8 : a 8 ∈ [0])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c12 : edge r12 (a 2) (a 18)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    : a 2 ∈ [0] ∧ a 10 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0,1] ∧ a 22 ∈ [0,1] ∧ a 23 ∈ [0] ∧ a 9 ∈ [0,2] := by
  have b0 : a 2 ≠ 1 := exclude [0,1] (edge r10) (a 2) (a 6) 1 d6 c10 (by decide +kernel)
  have t0 : a 2 ∈ [0,2] := remove (a 2) 1 [0,1,2] d2 b0
  have b1 : a 2 ≠ 2 := exclude [0,1] (edge r10) (a 2) (a 6) 2 d6 c10 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 2 [0,2] t0 b1
  have b2 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 t1 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b2
  have b3 : a 10 ≠ 3 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 3 t1 c11 (by decide +kernel)
  have t3 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t2 b3
  have b4 : a 18 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 1 t1 c12 (by decide +kernel)
  have t4 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b4
  have b5 : a 18 ≠ 2 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 2 t1 c12 (by decide +kernel)
  have t5 : a 18 ∈ [0,3] := remove (a 18) 2 [0,2,3] t4 b5
  have b6 : a 18 ≠ 3 := exclude [0] (fun u v => edge r12 v u) (a 18) (a 2) 3 t1 c12 (by decide +kernel)
  have t6 : a 18 ∈ [0] := remove (a 18) 3 [0,3] t5 b6
  have b7 : a 19 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 2 d3 c15 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,3] := remove (a 19) 2 [0,1,2,3] d19 b7
  have b8 : a 19 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 3 d3 c15 (by decide +kernel)
  have t8 : a 19 ∈ [0,1] := remove (a 19) 3 [0,1,3] t7 b8
  have b9 : a 22 ≠ 2 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,1,3,4,5] := remove (a 22) 2 [0,1,2,3,4,5] d22 b9
  have b10 : a 22 ≠ 3 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,1,4,5] := remove (a 22) 3 [0,1,3,4,5] t9 b10
  have b11 : a 22 ≠ 4 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 4 d6 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,1,5] := remove (a 22) 4 [0,1,4,5] t10 b11
  have b12 : a 22 ≠ 5 := exclude [0,1] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,1] := remove (a 22) 5 [0,1,5] t11 b12
  have b13 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 d7 c27 (by decide +kernel)
  have t13 : a 23 ∈ [0,2] := remove (a 23) 1 [0,1,2] d23 b13
  have b14 : a 23 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 2 d7 c27 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 2 [0,2] t13 b14
  have b15 : a 9 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 1 d8 c28 (by decide +kernel)
  have t15 : a 9 ∈ [0,2] := remove (a 9) 1 [0,1,2] d9 b15
  exact And.intro t1 (And.intro t3 (And.intro t6 (And.intro t8 (And.intro t12 (And.intro t14 (t15))))))

theorem chunk1 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,2])
    (d25 : a 25 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,2])
    (d14 : a 14 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d28 : a 28 ∈ [0,1,2])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (c30 : edge r30 (a 8) (a 12)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 12 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0,1,2] ∧ a 10 ∈ [0] ∧ a 14 ∈ [0,2] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 28 ∈ [0,2] ∧ a 29 ∈ [0,2,3,4,5] := by
  have b0 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 d8 c30 (by decide +kernel)
  have t0 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b0
  have b1 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 1 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [0,2,3,4,5] := remove (a 13) 1 [0,1,2,3,4,5] d13 b1
  have b2 : a 13 ≠ 4 := exclude [0,2] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t2 : a 13 ∈ [0,2,3,5] := remove (a 13) 4 [0,2,3,4,5] t1 b2
  have b3 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r34 v u) (a 25) (a 9) 3 d9 c34 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,2] := remove (a 25) 3 [0,1,2,3] d25 b3
  have b4 : a 10 ≠ 2 := exclude [0,1,2,3] (edge r36) (a 10) (a 14) 2 d14 c36 (by decide +kernel)
  have t4 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b4
  have b5 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 t4 c36 (by decide +kernel)
  have t5 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b5
  have b6 : a 14 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 3 t4 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t5 b6
  have b7 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t4 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b7
  have b8 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t4 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0,3] := remove (a 26) 2 [0,2,3] t7 b8
  have b9 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t4 c37 (by decide +kernel)
  have t9 : a 26 ∈ [0] := remove (a 26) 3 [0,3] t8 b9
  have b10 : a 15 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 1 d11 c38 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b10
  have b11 : a 13 ≠ 3 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 3 t0 c40 (by decide +kernel)
  have t11 : a 13 ∈ [0,2,5] := remove (a 13) 3 [0,2,3,5] t2 b11
  have b12 : a 13 ≠ 5 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 5 t0 c40 (by decide +kernel)
  have t12 : a 13 ∈ [0,2] := remove (a 13) 5 [0,2,5] t11 b12
  have b13 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t0 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0,2] := remove (a 28) 1 [0,1,2] d28 b13
  have b14 : a 13 ≠ 2 := exclude [0] (edge r43) (a 13) (a 15) 2 t10 c43 (by decide +kernel)
  have t14 : a 13 ∈ [0] := remove (a 13) 2 [0,2] t12 b14
  have b15 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 t14 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0,2,3,4,5] := remove (a 29) 1 [0,1,2,3,4,5] d29 b15
  exact And.intro t0 (And.intro t14 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t9 (And.intro t10 (And.intro t13 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,2,3,4,5])
    (d13 : a 13 ∈ [0])
    (d14 : a 14 ∈ [0,2])
    (d15 : a 15 ∈ [0])
    (d30 : a 30 ∈ [0,1,2])
    (d31 : a 31 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0])
    (d17 : a 17 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2])
    (d22 : a 22 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3,4,5])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    : a 29 ∈ [0,2] ∧ a 14 ∈ [0] ∧ a 30 ∈ [0,2] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0,1] ∧ a 25 ∈ [0,1] ∧ a 19 ∈ [0] ∧ a 22 ∈ [0] ∧ a 27 ∈ [0] ∧ a 20 ∈ [0,2,3,4,5] := by
  have b0 : a 29 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,4,5] := remove (a 29) 3 [0,2,3,4,5] d29 b0
  have b1 : a 29 ≠ 4 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0,2,5] := remove (a 29) 4 [0,2,4,5] t0 b1
  have b2 : a 29 ≠ 5 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t2 : a 29 ∈ [0,2] := remove (a 29) 5 [0,2,5] t1 b2
  have b3 : a 14 ≠ 2 := exclude [0] (edge r45) (a 14) (a 15) 2 d15 c45 (by decide +kernel)
  have t3 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b3
  have b4 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 t3 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0,2] := remove (a 30) 1 [0,1,2] d30 b4
  have b5 : a 31 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b5
  have b6 : a 16 ≠ 1 := exclude [0] (edge r49) (a 16) (a 18) 1 d18 c49 (by decide +kernel)
  have t6 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b6
  have b7 : a 16 ≠ 2 := exclude [0] (edge r49) (a 16) (a 18) 2 d18 c49 (by decide +kernel)
  have t7 : a 16 ∈ [0,3] := remove (a 16) 2 [0,2,3] t6 b7
  have b8 : a 16 ≠ 3 := exclude [0] (edge r49) (a 16) (a 18) 3 d18 c49 (by decide +kernel)
  have t8 : a 16 ∈ [0] := remove (a 16) 3 [0,3] t7 b8
  have b9 : a 17 ≠ 2 := exclude [0,1] (edge r52) (a 17) (a 19) 2 d19 c52 (by decide +kernel)
  have t9 : a 17 ∈ [0,1,3] := remove (a 17) 2 [0,1,2,3] d17 b9
  have b10 : a 17 ≠ 3 := exclude [0,1,2] (edge r54) (a 17) (a 25) 3 d25 c54 (by decide +kernel)
  have t10 : a 17 ∈ [0,1] := remove (a 17) 3 [0,1,3] t9 b10
  have b11 : a 25 ≠ 2 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 2 t10 c54 (by decide +kernel)
  have t11 : a 25 ∈ [0,1] := remove (a 25) 2 [0,1,2] d25 b11
  have b12 : a 19 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 1 d18 c55 (by decide +kernel)
  have t12 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b12
  have b13 : a 22 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 1 d18 c56 (by decide +kernel)
  have t13 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b13
  have b14 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 t12 c59 (by decide +kernel)
  have t14 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b14
  have b15 : a 20 ≠ 1 := exclude [0] (edge r61) (a 20) (a 22) 1 t13 c61 (by decide +kernel)
  have t15 : a 20 ∈ [0,2,3,4,5] := remove (a 20) 1 [0,1,2,3,4,5] d20 b15
  exact And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))))

theorem chunk3 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,2,3,4,5])
    (d22 : a 22 ∈ [0])
    (d28 : a 28 ∈ [0,2])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d23 : a 23 ∈ [0])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0,2])
    (d25 : a 25 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d6 : a 6 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 20 ∈ [0] ∧ a 28 ∈ [0] ∧ a 21 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 25 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 6 ∈ [0] := by
  have b0 : a 20 ≠ 2 := exclude [0] (edge r61) (a 20) (a 22) 2 d22 c61 (by decide +kernel)
  have t0 : a 20 ∈ [0,3,4,5] := remove (a 20) 2 [0,2,3,4,5] d20 b0
  have b1 : a 20 ≠ 3 := exclude [0] (edge r61) (a 20) (a 22) 3 d22 c61 (by decide +kernel)
  have t1 : a 20 ∈ [0,4,5] := remove (a 20) 3 [0,3,4,5] t0 b1
  have b2 : a 20 ≠ 4 := exclude [0] (edge r61) (a 20) (a 22) 4 d22 c61 (by decide +kernel)
  have t2 : a 20 ∈ [0,5] := remove (a 20) 4 [0,4,5] t1 b2
  have b3 : a 20 ≠ 5 := exclude [0] (edge r61) (a 20) (a 22) 5 d22 c61 (by decide +kernel)
  have t3 : a 20 ∈ [0] := remove (a 20) 5 [0,5] t2 b3
  have b4 : a 28 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 2 t3 c62 (by decide +kernel)
  have t4 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b4
  have b5 : a 21 ≠ 2 := exclude [0] (edge r63) (a 21) (a 23) 2 d23 c63 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b5
  have b6 : a 21 ≠ 3 := exclude [0] (edge r63) (a 21) (a 23) 3 d23 c63 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] t5 b6
  have b7 : a 21 ≠ 4 := exclude [0] (edge r63) (a 21) (a 23) 4 d23 c63 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t6 b7
  have b8 : a 21 ≠ 5 := exclude [0] (edge r63) (a 21) (a 23) 5 d23 c63 (by decide +kernel)
  have t8 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t7 b8
  have b9 : a 21 ≠ 1 := exclude [0,2] (edge r64) (a 21) (a 29) 1 d29 c64 (by decide +kernel)
  have t9 : a 21 ∈ [0] := remove (a 21) 1 [0,1] t8 b9
  have b10 : a 29 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 2 t9 c64 (by decide +kernel)
  have t10 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b10
  have b11 : a 30 ≠ 2 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 2 d22 c66 (by decide +kernel)
  have t11 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b11
  have b12 : a 25 ≠ 1 := exclude [0] (edge r72) (a 25) (a 29) 1 t10 c72 (by decide +kernel)
  have t12 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b12
  have b13 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t13 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b13
  have b14 : a 5 ≠ 1 := exclude [0] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t14 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b14
  have b15 : a 6 ≠ 1 := exclude [0] (edge r24) (a 6) (a 14) 1 d14 c24 (by decide +kernel)
  have t15 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b15
  exact And.intro t3 (And.intro t4 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))

theorem chunk4 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,2])
    (d25 : a 25 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (c34 : edge r34 (a 9) (a 25)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    : a 9 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 9 ≠ 2 := exclude [0] (edge r34) (a 9) (a 25) 2 d25 c34 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b0
  have b1 : a 17 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 1 d16 c48 (by decide +kernel)
  have t1 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b1
  exact And.intro t0 (t1)
theorem cover (a : Nat → Nat)
    (start0 : a 0 ∈ [0])
    (start1 : a 1 ∈ [0])
    (start2 : a 2 ∈ [0,1,2])
    (start3 : a 3 ∈ [0])
    (start4 : a 4 ∈ [0,1])
    (start5 : a 5 ∈ [0,1])
    (start6 : a 6 ∈ [0,1])
    (start7 : a 7 ∈ [0])
    (start8 : a 8 ∈ [0])
    (start9 : a 9 ∈ [0,1,2])
    (start10 : a 10 ∈ [0,1,2,3])
    (start11 : a 11 ∈ [0])
    (start12 : a 12 ∈ [0,1])
    (start13 : a 13 ∈ [0,1,2,3,4,5])
    (start14 : a 14 ∈ [0,1,2,3])
    (start15 : a 15 ∈ [0,1])
    (start16 : a 16 ∈ [0,1,2,3])
    (start17 : a 17 ∈ [0,1,2,3])
    (start18 : a 18 ∈ [0,1,2,3])
    (start19 : a 19 ∈ [0,1,2,3])
    (start20 : a 20 ∈ [0,1,2,3,4,5])
    (start21 : a 21 ∈ [0,1,2,3,4,5])
    (start22 : a 22 ∈ [0,1,2,3,4,5])
    (start23 : a 23 ∈ [0,1,2])
    (start24 : a 24 ∈ [0])
    (start25 : a 25 ∈ [0,1,2,3])
    (start26 : a 26 ∈ [0,1,2,3])
    (start27 : a 27 ∈ [0,1])
    (start28 : a 28 ∈ [0,1,2])
    (start29 : a 29 ∈ [0,1,2,3,4,5])
    (start30 : a 30 ∈ [0,1,2])
    (start31 : a 31 ∈ [0,1])
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
  have group1 := chunk0 a start2 start6 start10 start18 start19 start3 start22 start23 start7 start9 start8 c10 c11 c12 c15 c25 c27 c28
  rcases group1 with ⟨h2,h3,h4,h5,h6,h7,h8⟩
  have group9 := chunk1 a start12 start8 start13 h8 start25 h3 start14 start26 start15 start11 start28 start29 c30 c33 c34 c36 c37 c38 c40 c42 c43 c44
  rcases group9 with ⟨h10,h11,h12,h13,h14,h15,h16,h17,h18⟩
  have group19 := chunk2 a h18 h11 h14 h16 start30 start31 start16 h4 start17 h5 h12 h6 start27 start20 c44 c45 c46 c47 c49 c52 c54 c55 c56 c59 c61
  rcases group19 with ⟨h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30⟩
  have group31 := chunk3 a h30 h28 h17 start21 h7 h20 h22 h26 start4 h10 start5 h11 start6 h21 c18 c21 c24 c61 c62 c63 c64 c66 c72
  rcases group31 with ⟨h32,h33,h34,h35,h36,h37,h38,h39,h40⟩
  have group41 := chunk4 a h8 h37 h25 h24 c34 c48
  rcases group41 with ⟨h42,h43⟩
  exact And.intro (forced (a 0) 0 start0) (And.intro (forced (a 1) 0 start1) (And.intro (forced (a 2) 0 h2) (And.intro (forced (a 3) 0 start3) (And.intro (forced (a 4) 0 h38) (And.intro (forced (a 5) 0 h39) (And.intro (forced (a 6) 0 h40) (And.intro (forced (a 7) 0 start7) (And.intro (forced (a 8) 0 start8) (And.intro (forced (a 9) 0 h42) (And.intro (forced (a 10) 0 h13) (And.intro (forced (a 11) 0 start11) (And.intro (forced (a 12) 0 h10) (And.intro (forced (a 13) 0 h11) (And.intro (forced (a 14) 0 h21) (And.intro (forced (a 15) 0 h16) (And.intro (forced (a 16) 0 h24) (And.intro (forced (a 17) 0 h43) (And.intro (forced (a 18) 0 h4) (And.intro (forced (a 19) 0 h27) (And.intro (forced (a 20) 0 h32) (And.intro (forced (a 21) 0 h34) (And.intro (forced (a 22) 0 h28) (And.intro (forced (a 23) 0 h7) (And.intro (forced (a 24) 0 start24) (And.intro (forced (a 25) 0 h37) (And.intro (forced (a 26) 0 h15) (And.intro (forced (a 27) 0 h29) (And.intro (forced (a 28) 0 h33) (And.intro (forced (a 29) 0 h35) (And.intro (forced (a 30) 0 h36) (forced (a 31) 0 h23)))))))))))))))))))))))))))))))
#print axioms cover
end PartitionCover205_168
