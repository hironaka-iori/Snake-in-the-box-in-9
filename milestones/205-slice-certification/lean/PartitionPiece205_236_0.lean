import PartitionData205_236
namespace PartitionCover205_236
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0])
    (d7 : a 7 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0])
    (d9 : a 9 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1,2,3])
    (c12 : edge r12 (a 4) (a 18)=true)
    (c14 : edge r14 (a 5) (a 7)=true)
    (c15 : edge r15 (a 5) (a 9)=true)
    (c16 : edge r16 (a 5) (a 19)=true)
    (c22 : edge r22 (a 7) (a 8)=true)
    (c23 : edge r23 (a 7) (a 11)=true)
    (c25 : edge r25 (a 8) (a 22)=true)
    (c26 : edge r26 (a 8) (a 32)=true)
    (c27 : edge r27 (a 9) (a 10)=true)
    : a 4 ∈ [0,2] ∧ a 7 ∈ [0,2] ∧ a 9 ∈ [0,2] ∧ a 19 ∈ [0,2] ∧ a 8 ∈ [0] ∧ a 11 ∈ [0,2] ∧ a 22 ∈ [0,2] ∧ a 32 ∈ [0,1] ∧ a 10 ∈ [0,2,3] := by
  have b0 : a 4 ≠ 1 := exclude [0] (edge r12) (a 4) (a 18) 1 d18 c12 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (edge r12) (a 4) (a 18) 3 d18 c12 (by decide +kernel)
  have t1 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t0 b1
  have b2 : a 7 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 7) (a 5) 1 d5 c14 (by decide +kernel)
  have t2 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b2
  have b3 : a 7 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 7) (a 5) 3 d5 c14 (by decide +kernel)
  have t3 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t2 b3
  have b4 : a 9 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 9) (a 5) 1 d5 c15 (by decide +kernel)
  have t4 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b4
  have b5 : a 9 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 9) (a 5) 3 d5 c15 (by decide +kernel)
  have t5 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t4 b5
  have b6 : a 19 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 19) (a 5) 1 d5 c16 (by decide +kernel)
  have t6 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b6
  have b7 : a 19 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 19) (a 5) 3 d5 c16 (by decide +kernel)
  have t7 : a 19 ∈ [0,2] := remove (a 19) 3 [0,2,3] t6 b7
  have b8 : a 8 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 8) (a 7) 1 t3 c22 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b8
  have b9 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r23 v u) (a 11) (a 7) 1 t3 c23 (by decide +kernel)
  have t9 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b9
  have b10 : a 11 ≠ 3 := exclude [0,2] (fun u v => edge r23 v u) (a 11) (a 7) 3 t3 c23 (by decide +kernel)
  have t10 : a 11 ∈ [0,2] := remove (a 11) 3 [0,2,3] t9 b10
  have b11 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 8) 1 t8 c25 (by decide +kernel)
  have t11 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b11
  have b12 : a 22 ≠ 3 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 8) 3 t8 c25 (by decide +kernel)
  have t12 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t11 b12
  have b13 : a 32 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 32) (a 8) 2 t8 c26 (by decide +kernel)
  have t13 : a 32 ∈ [0,1,3] := remove (a 32) 2 [0,1,2,3] d32 b13
  have b14 : a 32 ≠ 3 := exclude [0] (fun u v => edge r26 v u) (a 32) (a 8) 3 t8 c26 (by decide +kernel)
  have t14 : a 32 ∈ [0,1] := remove (a 32) 3 [0,1,3] t13 b14
  have b15 : a 10 ≠ 1 := exclude [0,2] (fun u v => edge r27 v u) (a 10) (a 9) 1 t5 c27 (by decide +kernel)
  have t15 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk1 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,2,3])
    (d9 : a 9 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,2])
    (d35 : a 35 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1])
    (d37 : a 37 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0])
    (c27 : edge r27 (a 9) (a 10)=true)
    (c29 : edge r29 (a 9) (a 23)=true)
    (c31 : edge r31 (a 10) (a 34)=true)
    (c32 : edge r32 (a 11) (a 24)=true)
    (c33 : edge r33 (a 11) (a 35)=true)
    (c34 : edge r34 (a 12) (a 13)=true)
    (c37 : edge r37 (a 12) (a 37)=true)
    (c38 : edge r38 (a 13) (a 14)=true)
    (c52 : edge r52 (a 18) (a 25)=true)
    : a 10 ∈ [0,2] ∧ a 23 ∈ [0,2] ∧ a 34 ∈ [0] ∧ a 24 ∈ [0,2] ∧ a 35 ∈ [0,1] ∧ a 13 ∈ [0,2] ∧ a 37 ∈ [0,2] ∧ a 14 ∈ [0,2] ∧ a 25 ∈ [0,2] := by
  have b0 : a 10 ≠ 3 := exclude [0,2] (fun u v => edge r27 v u) (a 10) (a 9) 3 d9 c27 (by decide +kernel)
  have t0 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] d10 b0
  have b1 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r29 v u) (a 23) (a 9) 1 d9 c29 (by decide +kernel)
  have t1 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b1
  have b2 : a 23 ≠ 3 := exclude [0,2] (fun u v => edge r29 v u) (a 23) (a 9) 3 d9 c29 (by decide +kernel)
  have t2 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t1 b2
  have b3 : a 34 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 34) (a 10) 1 t0 c31 (by decide +kernel)
  have t3 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b3
  have b4 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r32 v u) (a 24) (a 11) 1 d11 c32 (by decide +kernel)
  have t4 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b4
  have b5 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r32 v u) (a 24) (a 11) 3 d11 c32 (by decide +kernel)
  have t5 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t4 b5
  have b6 : a 35 ≠ 2 := exclude [0,2] (fun u v => edge r33 v u) (a 35) (a 11) 2 d11 c33 (by decide +kernel)
  have t6 : a 35 ∈ [0,1,3] := remove (a 35) 2 [0,1,2,3] d35 b6
  have b7 : a 35 ≠ 3 := exclude [0,2] (fun u v => edge r33 v u) (a 35) (a 11) 3 d11 c33 (by decide +kernel)
  have t7 : a 35 ∈ [0,1] := remove (a 35) 3 [0,1,3] t6 b7
  have b8 : a 13 ≠ 1 := exclude [0,1] (fun u v => edge r34 v u) (a 13) (a 12) 1 d12 c34 (by decide +kernel)
  have t8 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b8
  have b9 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 13) (a 12) 3 d12 c34 (by decide +kernel)
  have t9 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t8 b9
  have b10 : a 37 ≠ 1 := exclude [0,1] (fun u v => edge r37 v u) (a 37) (a 12) 1 d12 c37 (by decide +kernel)
  have t10 : a 37 ∈ [0,2,3] := remove (a 37) 1 [0,1,2,3] d37 b10
  have b11 : a 37 ≠ 3 := exclude [0,1] (fun u v => edge r37 v u) (a 37) (a 12) 3 d12 c37 (by decide +kernel)
  have t11 : a 37 ∈ [0,2] := remove (a 37) 3 [0,2,3] t10 b11
  have b12 : a 14 ≠ 1 := exclude [0,2] (fun u v => edge r38 v u) (a 14) (a 13) 1 t9 c38 (by decide +kernel)
  have t12 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b12
  have b13 : a 14 ≠ 3 := exclude [0,2] (fun u v => edge r38 v u) (a 14) (a 13) 3 t9 c38 (by decide +kernel)
  have t13 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t12 b13
  have b14 : a 25 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 25) (a 18) 1 d18 c52 (by decide +kernel)
  have t14 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b14
  have b15 : a 25 ≠ 3 := exclude [0] (fun u v => edge r52 v u) (a 25) (a 18) 3 d18 c52 (by decide +kernel)
  have t15 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t13 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d20 : a 20 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,2])
    (d43 : a 43 ∈ [0,1,2,3])
    (d45 : a 45 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,2])
    (d46 : a 46 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d48 : a 48 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,2])
    (d29 : a 29 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0])
    (d36 : a 36 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1])
    (d47 : a 47 ∈ [0,1,2,3])
    (d38 : a 38 ∈ [0,1,2,3])
    (d37 : a 37 ∈ [0,2])
    (c54 : edge r54 (a 19) (a 20)=true)
    (c58 : edge r58 (a 20) (a 43)=true)
    (c63 : edge r63 (a 22) (a 45)=true)
    (c65 : edge r65 (a 23) (a 46)=true)
    (c67 : edge r67 (a 24) (a 48)=true)
    (c75 : edge r75 (a 29) (a 34)=true)
    (c81 : edge r81 (a 32) (a 36)=true)
    (c87 : edge r87 (a 34) (a 47)=true)
    (c91 : edge r91 (a 37) (a 38)=true)
    : a 20 ∈ [0,2] ∧ a 43 ∈ [0,2] ∧ a 45 ∈ [0,1] ∧ a 46 ∈ [0] ∧ a 48 ∈ [0,1] ∧ a 29 ∈ [0,1] ∧ a 36 ∈ [0,1] ∧ a 47 ∈ [0,2] ∧ a 38 ∈ [0,2,3] := by
  have b0 : a 20 ≠ 1 := exclude [0,2] (fun u v => edge r54 v u) (a 20) (a 19) 1 d19 c54 (by decide +kernel)
  have t0 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b0
  have b1 : a 20 ≠ 3 := exclude [0,2] (fun u v => edge r54 v u) (a 20) (a 19) 3 d19 c54 (by decide +kernel)
  have t1 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t0 b1
  have b2 : a 43 ≠ 1 := exclude [0,2] (fun u v => edge r58 v u) (a 43) (a 20) 1 t1 c58 (by decide +kernel)
  have t2 : a 43 ∈ [0,2,3] := remove (a 43) 1 [0,1,2,3] d43 b2
  have b3 : a 43 ≠ 3 := exclude [0,2] (fun u v => edge r58 v u) (a 43) (a 20) 3 t1 c58 (by decide +kernel)
  have t3 : a 43 ∈ [0,2] := remove (a 43) 3 [0,2,3] t2 b3
  have b4 : a 45 ≠ 2 := exclude [0,2] (fun u v => edge r63 v u) (a 45) (a 22) 2 d22 c63 (by decide +kernel)
  have t4 : a 45 ∈ [0,1,3] := remove (a 45) 2 [0,1,2,3] d45 b4
  have b5 : a 45 ≠ 3 := exclude [0,2] (fun u v => edge r63 v u) (a 45) (a 22) 3 d22 c63 (by decide +kernel)
  have t5 : a 45 ∈ [0,1] := remove (a 45) 3 [0,1,3] t4 b5
  have b6 : a 46 ≠ 1 := exclude [0,2] (fun u v => edge r65 v u) (a 46) (a 23) 1 d23 c65 (by decide +kernel)
  have t6 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b6
  have b7 : a 48 ≠ 2 := exclude [0,2] (fun u v => edge r67 v u) (a 48) (a 24) 2 d24 c67 (by decide +kernel)
  have t7 : a 48 ∈ [0,1,3] := remove (a 48) 2 [0,1,2,3] d48 b7
  have b8 : a 48 ≠ 3 := exclude [0,2] (fun u v => edge r67 v u) (a 48) (a 24) 3 d24 c67 (by decide +kernel)
  have t8 : a 48 ∈ [0,1] := remove (a 48) 3 [0,1,3] t7 b8
  have b9 : a 29 ≠ 2 := exclude [0] (edge r75) (a 29) (a 34) 2 d34 c75 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,3] := remove (a 29) 2 [0,1,2,3] d29 b9
  have b10 : a 29 ≠ 3 := exclude [0] (edge r75) (a 29) (a 34) 3 d34 c75 (by decide +kernel)
  have t10 : a 29 ∈ [0,1] := remove (a 29) 3 [0,1,3] t9 b10
  have b11 : a 36 ≠ 2 := exclude [0,1] (fun u v => edge r81 v u) (a 36) (a 32) 2 d32 c81 (by decide +kernel)
  have t11 : a 36 ∈ [0,1,3] := remove (a 36) 2 [0,1,2,3] d36 b11
  have b12 : a 36 ≠ 3 := exclude [0,1] (fun u v => edge r81 v u) (a 36) (a 32) 3 d32 c81 (by decide +kernel)
  have t12 : a 36 ∈ [0,1] := remove (a 36) 3 [0,1,3] t11 b12
  have b13 : a 47 ≠ 1 := exclude [0] (fun u v => edge r87 v u) (a 47) (a 34) 1 d34 c87 (by decide +kernel)
  have t13 : a 47 ∈ [0,2,3] := remove (a 47) 1 [0,1,2,3] d47 b13
  have b14 : a 47 ≠ 3 := exclude [0] (fun u v => edge r87 v u) (a 47) (a 34) 3 d34 c87 (by decide +kernel)
  have t14 : a 47 ∈ [0,2] := remove (a 47) 3 [0,2,3] t13 b14
  have b15 : a 38 ≠ 1 := exclude [0,2] (fun u v => edge r91 v u) (a 38) (a 37) 1 d37 c91 (by decide +kernel)
  have t15 : a 38 ∈ [0,2,3] := remove (a 38) 1 [0,1,2,3] d38 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk3 (a : Nat → Nat)
    (d38 : a 38 ∈ [0,2,3])
    (d37 : a 37 ∈ [0,2])
    (d44 : a 44 ∈ [0,1,2,3])
    (d39 : a 39 ∈ [0,1])
    (d3 : a 3 ∈ [0,1,2,3])
    (d4 : a 4 ∈ [0,2])
    (d28 : a 28 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1])
    (c9 : edge r9 (a 3) (a 4)=true)
    (c72 : edge r72 (a 28) (a 29)=true)
    (c91 : edge r91 (a 37) (a 38)=true)
    (c96 : edge r96 (a 39) (a 44)=true)
    : a 38 ∈ [0,2] ∧ a 44 ∈ [0,1] ∧ a 3 ∈ [0,2] ∧ a 28 ∈ [0,1] := by
  have b0 : a 38 ≠ 3 := exclude [0,2] (fun u v => edge r91 v u) (a 38) (a 37) 3 d37 c91 (by decide +kernel)
  have t0 : a 38 ∈ [0,2] := remove (a 38) 3 [0,2,3] d38 b0
  have b1 : a 44 ≠ 2 := exclude [0,1] (fun u v => edge r96 v u) (a 44) (a 39) 2 d39 c96 (by decide +kernel)
  have t1 : a 44 ∈ [0,1,3] := remove (a 44) 2 [0,1,2,3] d44 b1
  have b2 : a 44 ≠ 3 := exclude [0,1] (fun u v => edge r96 v u) (a 44) (a 39) 3 d39 c96 (by decide +kernel)
  have t2 : a 44 ∈ [0,1] := remove (a 44) 3 [0,1,3] t1 b2
  have b3 : a 3 ≠ 1 := exclude [0,2] (edge r9) (a 3) (a 4) 1 d4 c9 (by decide +kernel)
  have t3 : a 3 ∈ [0,2,3] := remove (a 3) 1 [0,1,2,3] d3 b3
  have b4 : a 3 ≠ 3 := exclude [0,2] (edge r9) (a 3) (a 4) 3 d4 c9 (by decide +kernel)
  have t4 : a 3 ∈ [0,2] := remove (a 3) 3 [0,2,3] t3 b4
  have b5 : a 28 ≠ 2 := exclude [0,1] (edge r72) (a 28) (a 29) 2 d29 c72 (by decide +kernel)
  have t5 : a 28 ∈ [0,1,3] := remove (a 28) 2 [0,1,2,3] d28 b5
  have b6 : a 28 ≠ 3 := exclude [0,1] (edge r72) (a 28) (a 29) 3 d29 c72 (by decide +kernel)
  have t6 : a 28 ∈ [0,1] := remove (a 28) 3 [0,1,3] t5 b6
  exact And.intro t0 (And.intro t2 (And.intro t4 (t6)))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_236
