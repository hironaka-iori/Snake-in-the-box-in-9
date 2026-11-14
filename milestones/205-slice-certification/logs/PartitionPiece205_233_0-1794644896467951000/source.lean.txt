import PartitionData205_233
namespace PartitionCover205_233
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1])
    (d32 : a 32 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c4 : edge r4 (a 0) (a 13)=true)
    (c5 : edge r5 (a 0) (a 28)=true)
    (c11 : edge r11 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 9)=true)
    (c13 : edge r13 (a 2) (a 15)=true)
    (c14 : edge r14 (a 2) (a 30)=true)
    (c21 : edge r21 (a 4) (a 17)=true)
    (c22 : edge r22 (a 4) (a 32)=true)
    : a 2 ∈ [0,2] ∧ a 4 ∈ [0,2] ∧ a 13 ∈ [0,2] ∧ a 28 ∈ [0,1] ∧ a 6 ∈ [0] ∧ a 9 ∈ [0] ∧ a 15 ∈ [0,2] ∧ a 30 ∈ [0,1] ∧ a 17 ∈ [0] ∧ a 32 ∈ [0] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b2
  have b3 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t2 b3
  have b4 : a 13 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 13) (a 0) 1 d0 c4 (by decide +kernel)
  have t4 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b4
  have b5 : a 13 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 13) (a 0) 3 d0 c4 (by decide +kernel)
  have t5 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t4 b5
  have b6 : a 28 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 28) (a 0) 2 d0 c5 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,3] := remove (a 28) 2 [0,1,2,3] d28 b6
  have b7 : a 28 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 28) (a 0) 3 d0 c5 (by decide +kernel)
  have t7 : a 28 ∈ [0,1] := remove (a 28) 3 [0,1,3] t6 b7
  have b8 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 6) (a 2) 1 t1 c11 (by decide +kernel)
  have t8 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b8
  have b9 : a 9 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 9) (a 2) 1 t1 c12 (by decide +kernel)
  have t9 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b9
  have b10 : a 15 ≠ 1 := exclude [0,2] (fun u v => edge r13 v u) (a 15) (a 2) 1 t1 c13 (by decide +kernel)
  have t10 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b10
  have b11 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 15) (a 2) 3 t1 c13 (by decide +kernel)
  have t11 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t10 b11
  have b12 : a 30 ≠ 2 := exclude [0,2] (fun u v => edge r14 v u) (a 30) (a 2) 2 t1 c14 (by decide +kernel)
  have t12 : a 30 ∈ [0,1,3] := remove (a 30) 2 [0,1,2,3] d30 b12
  have b13 : a 30 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 30) (a 2) 3 t1 c14 (by decide +kernel)
  have t13 : a 30 ∈ [0,1] := remove (a 30) 3 [0,1,3] t12 b13
  have b14 : a 17 ≠ 1 := exclude [0,2] (fun u v => edge r21 v u) (a 17) (a 4) 1 t3 c21 (by decide +kernel)
  have t14 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b14
  have b15 : a 32 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 32) (a 4) 1 t3 c22 (by decide +kernel)
  have t15 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t11 (And.intro t13 (And.intro t14 (t15)))))))))

theorem chunk1 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d12 : a 12 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0])
    (d23 : a 23 ∈ [0,1])
    (d38 : a 38 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,2,3])
    (d39 : a 39 ∈ [0,1])
    (c27 : edge r27 (a 6) (a 7)=true)
    (c28 : edge r28 (a 6) (a 12)=true)
    (c31 : edge r31 (a 7) (a 20)=true)
    (c32 : edge r32 (a 7) (a 35)=true)
    (c36 : edge r36 (a 9) (a 10)=true)
    (c38 : edge r38 (a 9) (a 23)=true)
    (c39 : edge r39 (a 9) (a 38)=true)
    (c40 : edge r40 (a 10) (a 24)=true)
    (c41 : edge r41 (a 10) (a 39)=true)
    : a 7 ∈ [0,2] ∧ a 12 ∈ [0,1] ∧ a 20 ∈ [0,2] ∧ a 35 ∈ [0,2] ∧ a 10 ∈ [0,2] ∧ a 23 ∈ [0] ∧ a 38 ∈ [0,1] ∧ a 24 ∈ [0,1] ∧ a 39 ∈ [0] := by
  have b0 : a 7 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 7) (a 6) 1 d6 c27 (by decide +kernel)
  have t0 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b0
  have b1 : a 7 ≠ 3 := exclude [0] (fun u v => edge r27 v u) (a 7) (a 6) 3 d6 c27 (by decide +kernel)
  have t1 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t0 b1
  have b2 : a 12 ≠ 2 := exclude [0] (fun u v => edge r28 v u) (a 12) (a 6) 2 d6 c28 (by decide +kernel)
  have t2 : a 12 ∈ [0,1,3] := remove (a 12) 2 [0,1,2,3] d12 b2
  have b3 : a 12 ≠ 3 := exclude [0] (fun u v => edge r28 v u) (a 12) (a 6) 3 d6 c28 (by decide +kernel)
  have t3 : a 12 ∈ [0,1] := remove (a 12) 3 [0,1,3] t2 b3
  have b4 : a 20 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 20) (a 7) 1 t1 c31 (by decide +kernel)
  have t4 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b4
  have b5 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r31 v u) (a 20) (a 7) 3 t1 c31 (by decide +kernel)
  have t5 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t4 b5
  have b6 : a 35 ≠ 1 := exclude [0,2] (fun u v => edge r32 v u) (a 35) (a 7) 1 t1 c32 (by decide +kernel)
  have t6 : a 35 ∈ [0,2,3] := remove (a 35) 1 [0,1,2,3] d35 b6
  have b7 : a 35 ≠ 3 := exclude [0,2] (fun u v => edge r32 v u) (a 35) (a 7) 3 t1 c32 (by decide +kernel)
  have t7 : a 35 ∈ [0,2] := remove (a 35) 3 [0,2,3] t6 b7
  have b8 : a 10 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 10) (a 9) 1 d9 c36 (by decide +kernel)
  have t8 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b8
  have b9 : a 10 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 10) (a 9) 3 d9 c36 (by decide +kernel)
  have t9 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t8 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 23) (a 9) 1 d9 c38 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b10
  have b11 : a 38 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 38) (a 9) 2 d9 c39 (by decide +kernel)
  have t11 : a 38 ∈ [0,1,3] := remove (a 38) 2 [0,1,2,3] d38 b11
  have b12 : a 38 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 38) (a 9) 3 d9 c39 (by decide +kernel)
  have t12 : a 38 ∈ [0,1] := remove (a 38) 3 [0,1,3] t11 b12
  have b13 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r40 v u) (a 24) (a 10) 2 t9 c40 (by decide +kernel)
  have t13 : a 24 ∈ [0,1,3] := remove (a 24) 2 [0,1,2,3] d24 b13
  have b14 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r40 v u) (a 24) (a 10) 3 t9 c40 (by decide +kernel)
  have t14 : a 24 ∈ [0,1] := remove (a 24) 3 [0,1,3] t13 b14
  have b15 : a 39 ≠ 1 := exclude [0,2] (fun u v => edge r41 v u) (a 39) (a 10) 1 t9 c41 (by decide +kernel)
  have t15 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d21 : a 21 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,2])
    (d44 : a 44 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
    (d46 : a 46 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1,2,3])
    (d49 : a 49 ∈ [0,1,2,3])
    (d51 : a 51 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,2])
    (c49 : edge r49 (a 13) (a 21)=true)
    (c50 : edge r50 (a 13) (a 44)=true)
    (c55 : edge r55 (a 15) (a 16)=true)
    (c58 : edge r58 (a 15) (a 46)=true)
    (c62 : edge r62 (a 17) (a 18)=true)
    (c64 : edge r64 (a 17) (a 25)=true)
    (c67 : edge r67 (a 18) (a 26)=true)
    (c68 : edge r68 (a 18) (a 49)=true)
    (c72 : edge r72 (a 20) (a 51)=true)
    : a 21 ∈ [0,2] ∧ a 44 ∈ [0,1] ∧ a 16 ∈ [0] ∧ a 46 ∈ [0,1] ∧ a 18 ∈ [0,1] ∧ a 25 ∈ [0,2] ∧ a 26 ∈ [0,1] ∧ a 49 ∈ [0,2] ∧ a 51 ∈ [0,1,3] := by
  have b0 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r49 v u) (a 21) (a 13) 1 d13 c49 (by decide +kernel)
  have t0 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b0
  have b1 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r49 v u) (a 21) (a 13) 3 d13 c49 (by decide +kernel)
  have t1 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] t0 b1
  have b2 : a 44 ≠ 2 := exclude [0,2] (fun u v => edge r50 v u) (a 44) (a 13) 2 d13 c50 (by decide +kernel)
  have t2 : a 44 ∈ [0,1,3] := remove (a 44) 2 [0,1,2,3] d44 b2
  have b3 : a 44 ≠ 3 := exclude [0,2] (fun u v => edge r50 v u) (a 44) (a 13) 3 d13 c50 (by decide +kernel)
  have t3 : a 44 ∈ [0,1] := remove (a 44) 3 [0,1,3] t2 b3
  have b4 : a 16 ≠ 1 := exclude [0,2] (fun u v => edge r55 v u) (a 16) (a 15) 1 d15 c55 (by decide +kernel)
  have t4 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b4
  have b5 : a 46 ≠ 2 := exclude [0,2] (fun u v => edge r58 v u) (a 46) (a 15) 2 d15 c58 (by decide +kernel)
  have t5 : a 46 ∈ [0,1,3] := remove (a 46) 2 [0,1,2,3] d46 b5
  have b6 : a 46 ≠ 3 := exclude [0,2] (fun u v => edge r58 v u) (a 46) (a 15) 3 d15 c58 (by decide +kernel)
  have t6 : a 46 ∈ [0,1] := remove (a 46) 3 [0,1,3] t5 b6
  have b7 : a 18 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 18) (a 17) 2 d17 c62 (by decide +kernel)
  have t7 : a 18 ∈ [0,1,3] := remove (a 18) 2 [0,1,2,3] d18 b7
  have b8 : a 18 ≠ 3 := exclude [0] (fun u v => edge r62 v u) (a 18) (a 17) 3 d17 c62 (by decide +kernel)
  have t8 : a 18 ∈ [0,1] := remove (a 18) 3 [0,1,3] t7 b8
  have b9 : a 25 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 25) (a 17) 1 d17 c64 (by decide +kernel)
  have t9 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b9
  have b10 : a 25 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 25) (a 17) 3 d17 c64 (by decide +kernel)
  have t10 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t9 b10
  have b11 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 26) (a 18) 2 t8 c67 (by decide +kernel)
  have t11 : a 26 ∈ [0,1,3] := remove (a 26) 2 [0,1,2,3] d26 b11
  have b12 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r67 v u) (a 26) (a 18) 3 t8 c67 (by decide +kernel)
  have t12 : a 26 ∈ [0,1] := remove (a 26) 3 [0,1,3] t11 b12
  have b13 : a 49 ≠ 1 := exclude [0,1] (fun u v => edge r68 v u) (a 49) (a 18) 1 t8 c68 (by decide +kernel)
  have t13 : a 49 ∈ [0,2,3] := remove (a 49) 1 [0,1,2,3] d49 b13
  have b14 : a 49 ≠ 3 := exclude [0,1] (fun u v => edge r68 v u) (a 49) (a 18) 3 t8 c68 (by decide +kernel)
  have t14 : a 49 ∈ [0,2] := remove (a 49) 3 [0,2,3] t13 b14
  have b15 : a 51 ≠ 2 := exclude [0,2] (fun u v => edge r72 v u) (a 51) (a 20) 2 d20 c72 (by decide +kernel)
  have t15 : a 51 ∈ [0,1,3] := remove (a 51) 2 [0,1,2,3] d51 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk3 (a : Nat → Nat)
    (d51 : a 51 ∈ [0,1,3])
    (d20 : a 20 ∈ [0,2])
    (d22 : a 22 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,2])
    (d52 : a 52 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d55 : a 55 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,2])
    (d36 : a 36 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d30 : a 30 ∈ [0,1])
    (d33 : a 33 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0])
    (d40 : a 40 ∈ [0,1])
    (d43 : a 43 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0,2])
    (d37 : a 37 ∈ [0,1,2,3])
    (c72 : edge r72 (a 20) (a 51)=true)
    (c73 : edge r73 (a 21) (a 22)=true)
    (c78 : edge r78 (a 22) (a 52)=true)
    (c81 : edge r81 (a 23) (a 53)=true)
    (c85 : edge r85 (a 25) (a 55)=true)
    (c91 : edge r91 (a 28) (a 36)=true)
    (c97 : edge r97 (a 30) (a 31)=true)
    (c104 : edge r104 (a 32) (a 33)=true)
    (c106 : edge r106 (a 32) (a 40)=true)
    (c114 : edge r114 (a 35) (a 43)=true)
    (c116 : edge r116 (a 36) (a 37)=true)
    : a 51 ∈ [0,1] ∧ a 22 ∈ [0,2] ∧ a 52 ∈ [0] ∧ a 53 ∈ [0] ∧ a 55 ∈ [0,1] ∧ a 36 ∈ [0,1] ∧ a 31 ∈ [0] ∧ a 33 ∈ [0,1] ∧ a 40 ∈ [0] ∧ a 43 ∈ [0,2] ∧ a 37 ∈ [0,2,3] := by
  have b0 : a 51 ≠ 3 := exclude [0,2] (fun u v => edge r72 v u) (a 51) (a 20) 3 d20 c72 (by decide +kernel)
  have t0 : a 51 ∈ [0,1] := remove (a 51) 3 [0,1,3] d51 b0
  have b1 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r73 v u) (a 22) (a 21) 1 d21 c73 (by decide +kernel)
  have t1 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b1
  have b2 : a 22 ≠ 3 := exclude [0,2] (fun u v => edge r73 v u) (a 22) (a 21) 3 d21 c73 (by decide +kernel)
  have t2 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t1 b2
  have b3 : a 52 ≠ 1 := exclude [0,2] (fun u v => edge r78 v u) (a 52) (a 22) 1 t2 c78 (by decide +kernel)
  have t3 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b3
  have b4 : a 53 ≠ 1 := exclude [0] (fun u v => edge r81 v u) (a 53) (a 23) 1 d23 c81 (by decide +kernel)
  have t4 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b4
  have b5 : a 55 ≠ 2 := exclude [0,2] (fun u v => edge r85 v u) (a 55) (a 25) 2 d25 c85 (by decide +kernel)
  have t5 : a 55 ∈ [0,1,3] := remove (a 55) 2 [0,1,2,3] d55 b5
  have b6 : a 55 ≠ 3 := exclude [0,2] (fun u v => edge r85 v u) (a 55) (a 25) 3 d25 c85 (by decide +kernel)
  have t6 : a 55 ∈ [0,1] := remove (a 55) 3 [0,1,3] t5 b6
  have b7 : a 36 ≠ 2 := exclude [0,1] (fun u v => edge r91 v u) (a 36) (a 28) 2 d28 c91 (by decide +kernel)
  have t7 : a 36 ∈ [0,1,3] := remove (a 36) 2 [0,1,2,3] d36 b7
  have b8 : a 36 ≠ 3 := exclude [0,1] (fun u v => edge r91 v u) (a 36) (a 28) 3 d28 c91 (by decide +kernel)
  have t8 : a 36 ∈ [0,1] := remove (a 36) 3 [0,1,3] t7 b8
  have b9 : a 31 ≠ 1 := exclude [0,1] (fun u v => edge r97 v u) (a 31) (a 30) 1 d30 c97 (by decide +kernel)
  have t9 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b9
  have b10 : a 33 ≠ 2 := exclude [0] (fun u v => edge r104 v u) (a 33) (a 32) 2 d32 c104 (by decide +kernel)
  have t10 : a 33 ∈ [0,1,3] := remove (a 33) 2 [0,1,2,3] d33 b10
  have b11 : a 33 ≠ 3 := exclude [0] (fun u v => edge r104 v u) (a 33) (a 32) 3 d32 c104 (by decide +kernel)
  have t11 : a 33 ∈ [0,1] := remove (a 33) 3 [0,1,3] t10 b11
  have b12 : a 40 ≠ 1 := exclude [0] (fun u v => edge r106 v u) (a 40) (a 32) 1 d32 c106 (by decide +kernel)
  have t12 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b12
  have b13 : a 43 ≠ 1 := exclude [0,2] (fun u v => edge r114 v u) (a 43) (a 35) 1 d35 c114 (by decide +kernel)
  have t13 : a 43 ∈ [0,2,3] := remove (a 43) 1 [0,1,2,3] d43 b13
  have b14 : a 43 ≠ 3 := exclude [0,2] (fun u v => edge r114 v u) (a 43) (a 35) 3 d35 c114 (by decide +kernel)
  have t14 : a 43 ∈ [0,2] := remove (a 43) 3 [0,2,3] t13 b14
  have b15 : a 37 ≠ 1 := exclude [0,1] (fun u v => edge r116 v u) (a 37) (a 36) 1 t8 c116 (by decide +kernel)
  have t15 : a 37 ∈ [0,2,3] := remove (a 37) 1 [0,1,2,3] d37 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t14 (t15))))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_233
