import PartitionData205_239
namespace PartitionCover205_239
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d32 : a 32 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 15)=true)
    (c4 : edge r4 (a 0) (a 31)=true)
    (c6 : edge r6 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 16)=true)
    (c9 : edge r9 (a 1) (a 32)=true)
    (c11 : edge r11 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 9)=true)
    (c13 : edge r13 (a 2) (a 17)=true)
    : a 2 ∈ [0] ∧ a 4 ∈ [0] ∧ a 15 ∈ [0] ∧ a 31 ∈ [0] ∧ a 5 ∈ [0] ∧ a 16 ∈ [0] ∧ a 32 ∈ [0] ∧ a 6 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b1
  have b2 : a 4 ≠ 2 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 2 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,3] := remove (a 4) 2 [0,2,3] t1 b2
  have b3 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 3 [0,3] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 15) (a 0) 1 d0 c3 (by decide +kernel)
  have t4 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b4
  have b5 : a 15 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 15) (a 0) 2 d0 c3 (by decide +kernel)
  have t5 : a 15 ∈ [0,3] := remove (a 15) 2 [0,2,3] t4 b5
  have b6 : a 15 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 15) (a 0) 3 d0 c3 (by decide +kernel)
  have t6 : a 15 ∈ [0] := remove (a 15) 3 [0,3] t5 b6
  have b7 : a 31 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 31) (a 0) 1 d0 c4 (by decide +kernel)
  have t7 : a 31 ∈ [0,2,3] := remove (a 31) 1 [0,1,2,3] d31 b7
  have b8 : a 31 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 31) (a 0) 2 d0 c4 (by decide +kernel)
  have t8 : a 31 ∈ [0,3] := remove (a 31) 2 [0,2,3] t7 b8
  have b9 : a 31 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 31) (a 0) 3 d0 c4 (by decide +kernel)
  have t9 : a 31 ∈ [0] := remove (a 31) 3 [0,3] t8 b9
  have b10 : a 5 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 1 d1 c6 (by decide +kernel)
  have t10 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b10
  have b11 : a 16 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 16) (a 1) 1 d1 c8 (by decide +kernel)
  have t11 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b11
  have b12 : a 32 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 32) (a 1) 1 d1 c9 (by decide +kernel)
  have t12 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b12
  have b13 : a 6 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 6) (a 2) 1 t0 c11 (by decide +kernel)
  have t13 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b13
  have b14 : a 9 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 9) (a 2) 1 t0 c12 (by decide +kernel)
  have t14 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b14
  have b15 : a 17 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 17) (a 2) 1 t0 c13 (by decide +kernel)
  have t15 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b15
  exact And.intro t0 (And.intro t3 (And.intro t6 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))

theorem chunk1 (a : Nat → Nat)
    (d33 : a 33 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d19 : a 19 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1])
    (d5 : a 5 ∈ [0])
    (d36 : a 36 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3])
    (d37 : a 37 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (c14 : edge r14 (a 2) (a 33)=true)
    (c21 : edge r21 (a 4) (a 11)=true)
    (c22 : edge r22 (a 4) (a 19)=true)
    (c23 : edge r23 (a 4) (a 35)=true)
    (c26 : edge r26 (a 5) (a 20)=true)
    (c27 : edge r27 (a 5) (a 36)=true)
    (c29 : edge r29 (a 6) (a 13)=true)
    (c30 : edge r30 (a 6) (a 21)=true)
    (c31 : edge r31 (a 6) (a 37)=true)
    (c41 : edge r41 (a 9) (a 25)=true)
    : a 33 ∈ [0] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 35 ∈ [0] ∧ a 20 ∈ [0] ∧ a 36 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 37 ∈ [0] ∧ a 25 ∈ [0] := by
  have b0 : a 33 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 33) (a 2) 1 d2 c14 (by decide +kernel)
  have t0 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b0
  have b1 : a 11 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 11) (a 4) 1 d4 c21 (by decide +kernel)
  have t1 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b1
  have b2 : a 19 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 19) (a 4) 1 d4 c22 (by decide +kernel)
  have t2 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b2
  have b3 : a 19 ≠ 2 := exclude [0] (fun u v => edge r22 v u) (a 19) (a 4) 2 d4 c22 (by decide +kernel)
  have t3 : a 19 ∈ [0,3] := remove (a 19) 2 [0,2,3] t2 b3
  have b4 : a 19 ≠ 3 := exclude [0] (fun u v => edge r22 v u) (a 19) (a 4) 3 d4 c22 (by decide +kernel)
  have t4 : a 19 ∈ [0] := remove (a 19) 3 [0,3] t3 b4
  have b5 : a 35 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 35) (a 4) 1 d4 c23 (by decide +kernel)
  have t5 : a 35 ∈ [0,2,3] := remove (a 35) 1 [0,1,2,3] d35 b5
  have b6 : a 35 ≠ 2 := exclude [0] (fun u v => edge r23 v u) (a 35) (a 4) 2 d4 c23 (by decide +kernel)
  have t6 : a 35 ∈ [0,3] := remove (a 35) 2 [0,2,3] t5 b6
  have b7 : a 35 ≠ 3 := exclude [0] (fun u v => edge r23 v u) (a 35) (a 4) 3 d4 c23 (by decide +kernel)
  have t7 : a 35 ∈ [0] := remove (a 35) 3 [0,3] t6 b7
  have b8 : a 20 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 20) (a 5) 1 d5 c26 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b8
  have b9 : a 36 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 36) (a 5) 1 d5 c27 (by decide +kernel)
  have t9 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b9
  have b10 : a 13 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 13) (a 6) 1 d6 c29 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b10
  have b11 : a 21 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 21) (a 6) 1 d6 c30 (by decide +kernel)
  have t11 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b11
  have b12 : a 21 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 21) (a 6) 2 d6 c30 (by decide +kernel)
  have t12 : a 21 ∈ [0,3] := remove (a 21) 2 [0,2,3] t11 b12
  have b13 : a 21 ≠ 3 := exclude [0] (fun u v => edge r30 v u) (a 21) (a 6) 3 d6 c30 (by decide +kernel)
  have t13 : a 21 ∈ [0] := remove (a 21) 3 [0,3] t12 b13
  have b14 : a 37 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 37) (a 6) 1 d6 c31 (by decide +kernel)
  have t14 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b14
  have b15 : a 25 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 25) (a 9) 1 d9 c41 (by decide +kernel)
  have t15 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b15
  exact And.intro t0 (And.intro t1 (And.intro t4 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t13 (And.intro t14 (t15)))))))))

theorem chunk2 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3])
    (d43 : a 43 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d28 : a 28 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1])
    (d46 : a 46 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0])
    (d47 : a 47 ∈ [0,1,2,3])
    (c44 : edge r44 (a 10) (a 26)=true)
    (c46 : edge r46 (a 11) (a 12)=true)
    (c48 : edge r48 (a 11) (a 27)=true)
    (c49 : edge r49 (a 11) (a 43)=true)
    (c50 : edge r50 (a 12) (a 14)=true)
    (c51 : edge r51 (a 12) (a 28)=true)
    (c56 : edge r56 (a 14) (a 30)=true)
    (c57 : edge r57 (a 14) (a 46)=true)
    (c61 : edge r61 (a 15) (a 23)=true)
    (c62 : edge r62 (a 15) (a 47)=true)
    : a 26 ∈ [0,2] ∧ a 12 ∈ [0] ∧ a 27 ∈ [0,2] ∧ a 43 ∈ [0] ∧ a 14 ∈ [0] ∧ a 28 ∈ [0,2] ∧ a 30 ∈ [0] ∧ a 46 ∈ [0,1] ∧ a 23 ∈ [0] ∧ a 47 ∈ [0,2,3] := by
  have b0 : a 26 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 26) (a 10) 1 d10 c44 (by decide +kernel)
  have t0 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b0
  have b1 : a 26 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 26) (a 10) 3 d10 c44 (by decide +kernel)
  have t1 : a 26 ∈ [0,2] := remove (a 26) 3 [0,2,3] t0 b1
  have b2 : a 12 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 12) (a 11) 1 d11 c46 (by decide +kernel)
  have t2 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b2
  have b3 : a 27 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 27) (a 11) 1 d11 c48 (by decide +kernel)
  have t3 : a 27 ∈ [0,2,3] := remove (a 27) 1 [0,1,2,3] d27 b3
  have b4 : a 27 ≠ 3 := exclude [0] (fun u v => edge r48 v u) (a 27) (a 11) 3 d11 c48 (by decide +kernel)
  have t4 : a 27 ∈ [0,2] := remove (a 27) 3 [0,2,3] t3 b4
  have b5 : a 43 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 43) (a 11) 1 d11 c49 (by decide +kernel)
  have t5 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b5
  have b6 : a 14 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 14) (a 12) 1 t2 c50 (by decide +kernel)
  have t6 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b6
  have b7 : a 28 ≠ 1 := exclude [0] (fun u v => edge r51 v u) (a 28) (a 12) 1 t2 c51 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b7
  have b8 : a 28 ≠ 3 := exclude [0] (fun u v => edge r51 v u) (a 28) (a 12) 3 t2 c51 (by decide +kernel)
  have t8 : a 28 ∈ [0,2] := remove (a 28) 3 [0,2,3] t7 b8
  have b9 : a 30 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 30) (a 14) 1 t6 c56 (by decide +kernel)
  have t9 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b9
  have b10 : a 46 ≠ 2 := exclude [0] (fun u v => edge r57 v u) (a 46) (a 14) 2 t6 c57 (by decide +kernel)
  have t10 : a 46 ∈ [0,1,3] := remove (a 46) 2 [0,1,2,3] d46 b10
  have b11 : a 46 ≠ 3 := exclude [0] (fun u v => edge r57 v u) (a 46) (a 14) 3 t6 c57 (by decide +kernel)
  have t11 : a 46 ∈ [0,1] := remove (a 46) 3 [0,1,3] t10 b11
  have b12 : a 23 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 23) (a 15) 1 d15 c61 (by decide +kernel)
  have t12 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b12
  have b13 : a 23 ≠ 2 := exclude [0] (fun u v => edge r61 v u) (a 23) (a 15) 2 d15 c61 (by decide +kernel)
  have t13 : a 23 ∈ [0,3] := remove (a 23) 2 [0,2,3] t12 b13
  have b14 : a 23 ≠ 3 := exclude [0] (fun u v => edge r61 v u) (a 23) (a 15) 3 d15 c61 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 3 [0,3] t13 b14
  have b15 : a 47 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 47) (a 15) 1 d15 c62 (by decide +kernel)
  have t15 : a 47 ∈ [0,2,3] := remove (a 47) 1 [0,1,2,3] d47 b15
  exact And.intro t1 (And.intro t2 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t11 (And.intro t14 (t15)))))))))

theorem chunk3 (a : Nat → Nat)
    (d47 : a 47 ∈ [0,2,3])
    (d15 : a 15 ∈ [0])
    (d24 : a 24 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0])
    (d18 : a 18 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d49 : a 49 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1])
    (d26 : a 26 ∈ [0,2])
    (d27 : a 27 ∈ [0,2])
    (d19 : a 19 ∈ [0])
    (d51 : a 51 ∈ [0,1])
    (d28 : a 28 ∈ [0,2])
    (d20 : a 20 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d53 : a 53 ∈ [0,1,2,3])
    (c62 : edge r62 (a 15) (a 47)=true)
    (c65 : edge r65 (a 16) (a 24)=true)
    (c67 : edge r67 (a 17) (a 18)=true)
    (c70 : edge r70 (a 17) (a 49)=true)
    (c71 : edge r71 (a 18) (a 22)=true)
    (c72 : edge r72 (a 18) (a 26)=true)
    (c76 : edge r76 (a 19) (a 27)=true)
    (c77 : edge r77 (a 19) (a 51)=true)
    (c79 : edge r79 (a 20) (a 28)=true)
    (c82 : edge r82 (a 21) (a 29)=true)
    (c83 : edge r83 (a 21) (a 53)=true)
    : a 47 ∈ [0] ∧ a 24 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 49 ∈ [0,1] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 51 ∈ [0] ∧ a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 53 ∈ [0] := by
  have b0 : a 47 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 47) (a 15) 2 d15 c62 (by decide +kernel)
  have t0 : a 47 ∈ [0,3] := remove (a 47) 2 [0,2,3] d47 b0
  have b1 : a 47 ≠ 3 := exclude [0] (fun u v => edge r62 v u) (a 47) (a 15) 3 d15 c62 (by decide +kernel)
  have t1 : a 47 ∈ [0] := remove (a 47) 3 [0,3] t0 b1
  have b2 : a 24 ≠ 1 := exclude [0] (fun u v => edge r65 v u) (a 24) (a 16) 1 d16 c65 (by decide +kernel)
  have t2 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b2
  have b3 : a 24 ≠ 3 := exclude [0] (fun u v => edge r65 v u) (a 24) (a 16) 3 d16 c65 (by decide +kernel)
  have t3 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t2 b3
  have b4 : a 18 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 18) (a 17) 1 d17 c67 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b4
  have b5 : a 49 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 49) (a 17) 2 d17 c70 (by decide +kernel)
  have t5 : a 49 ∈ [0,1,3] := remove (a 49) 2 [0,1,2,3] d49 b5
  have b6 : a 49 ≠ 3 := exclude [0] (fun u v => edge r70 v u) (a 49) (a 17) 3 d17 c70 (by decide +kernel)
  have t6 : a 49 ∈ [0,1] := remove (a 49) 3 [0,1,3] t5 b6
  have b7 : a 22 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 22) (a 18) 1 t4 c71 (by decide +kernel)
  have t7 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b7
  have b8 : a 26 ≠ 2 := exclude [0] (fun u v => edge r72 v u) (a 26) (a 18) 2 t4 c72 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b8
  have b9 : a 27 ≠ 2 := exclude [0] (fun u v => edge r76 v u) (a 27) (a 19) 2 d19 c76 (by decide +kernel)
  have t9 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b9
  have b10 : a 51 ≠ 1 := exclude [0] (fun u v => edge r77 v u) (a 51) (a 19) 1 d19 c77 (by decide +kernel)
  have t10 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b10
  have b11 : a 28 ≠ 2 := exclude [0] (fun u v => edge r79 v u) (a 28) (a 20) 2 d20 c79 (by decide +kernel)
  have t11 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b11
  have b12 : a 29 ≠ 1 := exclude [0] (fun u v => edge r82 v u) (a 29) (a 21) 1 d21 c82 (by decide +kernel)
  have t12 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b12
  have b13 : a 53 ≠ 1 := exclude [0] (fun u v => edge r83 v u) (a 53) (a 21) 1 d21 c83 (by decide +kernel)
  have t13 : a 53 ∈ [0,2,3] := remove (a 53) 1 [0,1,2,3] d53 b13
  have b14 : a 53 ≠ 2 := exclude [0] (fun u v => edge r83 v u) (a 53) (a 21) 2 d21 c83 (by decide +kernel)
  have t14 : a 53 ∈ [0,3] := remove (a 53) 2 [0,2,3] t13 b14
  have b15 : a 53 ≠ 3 := exclude [0] (fun u v => edge r83 v u) (a 53) (a 21) 3 d21 c83 (by decide +kernel)
  have t15 : a 53 ∈ [0] := remove (a 53) 3 [0,3] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t15))))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_239
