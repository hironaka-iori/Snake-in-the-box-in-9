import PartitionData205_181
namespace PartitionCover205_181
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,4,8])
    (d17 : a 17 ∈ [0,1])
    (d20 : a 20 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1,2])
    (d21 : a 21 ∈ [0,1])
    (d29 : a 29 ∈ [0,2])
    (d23 : a 23 ∈ [0,2,6,8])
    (d30 : a 30 ∈ [0,1,2,6,7,8])
    (d31 : a 31 ∈ [0,1,2,3,5,7,11,12,13,14,15,16,17,21,22,23])
    (c54 : edge r54 (a 17) (a 25)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 25 ∈ [0,4] ∧ a 20 ∈ [0,2] ∧ a 22 ∈ [0] ∧ a 21 ∈ [0] ∧ a 23 ∈ [0,6] ∧ a 30 ∈ [0,1,6,7] ∧ a 31 ∈ [0,2,12,14,15,16,17,21,22,23] := by
  have b0 : a 25 ≠ 8 := exclude [0,1] (fun u v => edge r54 v u) (a 25) (a 17) 8 d17 c54 (by decide +kernel)
  have t0 : a 25 ∈ [0,4] := remove (a 25) 8 [0,4,8] d25 b0
  have b1 : a 20 ≠ 1 := exclude [0,1,2] (edge r61) (a 20) (a 22) 1 d22 c61 (by decide +kernel)
  have t1 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b1
  have b2 : a 20 ≠ 3 := exclude [0,1,2] (edge r61) (a 20) (a 22) 3 d22 c61 (by decide +kernel)
  have t2 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t1 b2
  have b3 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r61 v u) (a 22) (a 20) 1 t2 c61 (by decide +kernel)
  have t3 : a 22 ∈ [0,2] := remove (a 22) 1 [0,1,2] d22 b3
  have b4 : a 22 ≠ 2 := exclude [0,2] (fun u v => edge r61 v u) (a 22) (a 20) 2 t2 c61 (by decide +kernel)
  have t4 : a 22 ∈ [0] := remove (a 22) 2 [0,2] t3 b4
  have b5 : a 21 ≠ 1 := exclude [0,2] (edge r64) (a 21) (a 29) 1 d29 c64 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b5
  have b6 : a 23 ≠ 2 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 2 t4 c65 (by decide +kernel)
  have t6 : a 23 ∈ [0,6,8] := remove (a 23) 2 [0,2,6,8] d23 b6
  have b7 : a 23 ≠ 8 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 8 t4 c65 (by decide +kernel)
  have t7 : a 23 ∈ [0,6] := remove (a 23) 8 [0,6,8] t6 b7
  have b8 : a 30 ≠ 2 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 2 t4 c66 (by decide +kernel)
  have t8 : a 30 ∈ [0,1,6,7,8] := remove (a 30) 2 [0,1,2,6,7,8] d30 b8
  have b9 : a 30 ≠ 8 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 8 t4 c66 (by decide +kernel)
  have t9 : a 30 ∈ [0,1,6,7] := remove (a 30) 8 [0,1,6,7,8] t8 b9
  have b10 : a 31 ≠ 1 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 1 t7 c67 (by decide +kernel)
  have t10 : a 31 ∈ [0,2,3,5,7,11,12,13,14,15,16,17,21,22,23] := remove (a 31) 1 [0,1,2,3,5,7,11,12,13,14,15,16,17,21,22,23] d31 b10
  have b11 : a 31 ≠ 3 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 3 t7 c67 (by decide +kernel)
  have t11 : a 31 ∈ [0,2,5,7,11,12,13,14,15,16,17,21,22,23] := remove (a 31) 3 [0,2,3,5,7,11,12,13,14,15,16,17,21,22,23] t10 b11
  have b12 : a 31 ≠ 5 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 5 t7 c67 (by decide +kernel)
  have t12 : a 31 ∈ [0,2,7,11,12,13,14,15,16,17,21,22,23] := remove (a 31) 5 [0,2,5,7,11,12,13,14,15,16,17,21,22,23] t11 b12
  have b13 : a 31 ≠ 7 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 7 t7 c67 (by decide +kernel)
  have t13 : a 31 ∈ [0,2,11,12,13,14,15,16,17,21,22,23] := remove (a 31) 7 [0,2,7,11,12,13,14,15,16,17,21,22,23] t12 b13
  have b14 : a 31 ≠ 11 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 11 t7 c67 (by decide +kernel)
  have t14 : a 31 ∈ [0,2,12,13,14,15,16,17,21,22,23] := remove (a 31) 11 [0,2,11,12,13,14,15,16,17,21,22,23] t13 b14
  have b15 : a 31 ≠ 13 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 13 t7 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,2,12,14,15,16,17,21,22,23] := remove (a 31) 13 [0,2,12,13,14,15,16,17,21,22,23] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t9 (t15))))))

theorem chunk13 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,2,12,14,15,16,17,21,22,23])
    (d23 : a 23 ∈ [0,6])
    (d25 : a 25 ∈ [0,4])
    (d24 : a 24 ∈ [0,6])
    (d26 : a 26 ∈ [0,1,3,4])
    (d30 : a 30 ∈ [0,1,6,7])
    (d27 : a 27 ∈ [0])
    (d28 : a 28 ∈ [0,1,2])
    (d29 : a 29 ∈ [0,2])
    (d5 : a 5 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 31 ∈ [0,2] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0,3] ∧ a 30 ∈ [0,6] ∧ a 28 ∈ [0,1] ∧ a 5 ∈ [0,2] := by
  have b0 : a 31 ≠ 14 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 14 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,2,12,15,16,17,21,22,23] := remove (a 31) 14 [0,2,12,14,15,16,17,21,22,23] d31 b0
  have b1 : a 31 ≠ 15 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 15 d23 c67 (by decide +kernel)
  have t1 : a 31 ∈ [0,2,12,16,17,21,22,23] := remove (a 31) 15 [0,2,12,15,16,17,21,22,23] t0 b1
  have b2 : a 31 ≠ 16 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 16 d23 c67 (by decide +kernel)
  have t2 : a 31 ∈ [0,2,12,17,21,22,23] := remove (a 31) 16 [0,2,12,16,17,21,22,23] t1 b2
  have b3 : a 31 ≠ 17 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 17 d23 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0,2,12,21,22,23] := remove (a 31) 17 [0,2,12,17,21,22,23] t2 b3
  have b4 : a 31 ≠ 21 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 21 d23 c67 (by decide +kernel)
  have t4 : a 31 ∈ [0,2,12,22,23] := remove (a 31) 21 [0,2,12,21,22,23] t3 b4
  have b5 : a 31 ≠ 23 := exclude [0,6] (fun u v => edge r67 v u) (a 31) (a 23) 23 d23 c67 (by decide +kernel)
  have t5 : a 31 ∈ [0,2,12,22] := remove (a 31) 23 [0,2,12,22,23] t4 b5
  have b6 : a 25 ≠ 4 := exclude [0,6] (fun u v => edge r68 v u) (a 25) (a 24) 4 d24 c68 (by decide +kernel)
  have t6 : a 25 ∈ [0] := remove (a 25) 4 [0,4] d25 b6
  have b7 : a 26 ≠ 1 := exclude [0,6] (fun u v => edge r69 v u) (a 26) (a 24) 1 d24 c69 (by decide +kernel)
  have t7 : a 26 ∈ [0,3,4] := remove (a 26) 1 [0,1,3,4] d26 b7
  have b8 : a 26 ≠ 4 := exclude [0,6] (fun u v => edge r69 v u) (a 26) (a 24) 4 d24 c69 (by decide +kernel)
  have t8 : a 26 ∈ [0,3] := remove (a 26) 4 [0,3,4] t7 b8
  have b9 : a 30 ≠ 1 := exclude [0,3] (fun u v => edge r74 v u) (a 30) (a 26) 1 t8 c74 (by decide +kernel)
  have t9 : a 30 ∈ [0,6,7] := remove (a 30) 1 [0,1,6,7] d30 b9
  have b10 : a 30 ≠ 7 := exclude [0,3] (fun u v => edge r74 v u) (a 30) (a 26) 7 t8 c74 (by decide +kernel)
  have t10 : a 30 ∈ [0,6] := remove (a 30) 7 [0,6,7] t9 b10
  have b11 : a 31 ≠ 12 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 12 d27 c75 (by decide +kernel)
  have t11 : a 31 ∈ [0,2,22] := remove (a 31) 12 [0,2,12,22] t5 b11
  have b12 : a 31 ≠ 22 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 22 d27 c75 (by decide +kernel)
  have t12 : a 31 ∈ [0,2] := remove (a 31) 22 [0,2,22] t11 b12
  have b13 : a 28 ≠ 2 := exclude [0,2] (edge r76) (a 28) (a 29) 2 d29 c76 (by decide +kernel)
  have t13 : a 28 ∈ [0,1] := remove (a 28) 2 [0,1,2] d28 b13
  have b14 : a 5 ≠ 1 := exclude [0] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t14 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b14
  have b15 : a 5 ≠ 3 := exclude [0] (edge r21) (a 5) (a 13) 3 d13 c21 (by decide +kernel)
  have t15 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t14 b15
  exact And.intro t12 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t13 (t15)))))

theorem chunk14 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,3])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d8 : a 8 ∈ [0,6])
    (d10 : a 10 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d24 : a 24 ∈ [0,6])
    (d11 : a 11 ∈ [0,6])
    (d14 : a 14 ∈ [0,4])
    (d26 : a 26 ∈ [0,3])
    (d15 : a 15 ∈ [0,12])
    (d30 : a 30 ∈ [0,6])
    (d31 : a 31 ∈ [0,2])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d23 : a 23 ∈ [0,6])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    : a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0] ∧ a 11 ∈ [0] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0] ∧ a 23 ∈ [0] := by
  have b0 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 3 [0,3] d9 b0
  have b1 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b1
  have b2 : a 8 ≠ 6 := exclude [0] (edge r28) (a 8) (a 9) 6 t0 c28 (by decide +kernel)
  have t2 : a 8 ∈ [0] := remove (a 8) 6 [0,6] d8 b2
  have b3 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 t2 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b3
  have b4 : a 12 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 2 t2 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b4
  have b5 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 t2 c31 (by decide +kernel)
  have t5 : a 24 ∈ [0] := remove (a 24) 6 [0,6] d24 b5
  have b6 : a 11 ≠ 6 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 6 t0 c32 (by decide +kernel)
  have t6 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b6
  have b7 : a 14 ≠ 4 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 4 t3 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 4 [0,4] d14 b7
  have b8 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t3 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 3 [0,3] d26 b8
  have b9 : a 15 ≠ 12 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 12 t6 c38 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 12 [0,12] d15 b9
  have b10 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 t7 c46 (by decide +kernel)
  have t10 : a 30 ∈ [0] := remove (a 30) 6 [0,6] d30 b10
  have b11 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 t9 c47 (by decide +kernel)
  have t11 : a 31 ∈ [0] := remove (a 31) 2 [0,2] d31 b11
  have b12 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 17) 1 t1 c48 (by decide +kernel)
  have t12 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b12
  have b13 : a 18 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 1 t12 c49 (by decide +kernel)
  have t13 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b13
  have b14 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 1 t1 c52 (by decide +kernel)
  have t14 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b14
  have b15 : a 23 ≠ 6 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 6 t14 c58 (by decide +kernel)
  have t15 : a 23 ∈ [0] := remove (a 23) 6 [0,6] d23 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1])
    (d30 : a 30 ∈ [0])
    (d29 : a 29 ∈ [0,2])
    (d31 : a 31 ∈ [0])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d20 : a 20 ∈ [0,2])
    (d6 : a 6 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d7 : a 7 ∈ [0,3])
    (d15 : a 15 ∈ [0])
    (d5 : a 5 ∈ [0,2])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 3 ∈ [0] ∧ a 4 ∈ [0] ∧ a 20 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 28 ≠ 1 := exclude [0] (edge r77) (a 28) (a 30) 1 d30 c77 (by decide +kernel)
  have t0 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b0
  have b1 : a 29 ≠ 2 := exclude [0] (edge r78) (a 29) (a 31) 2 d31 c78 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b1
  have b2 : a 3 ≠ 1 := exclude [0] (edge r14) (a 3) (a 11) 1 d11 c14 (by decide +kernel)
  have t2 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b2
  have b3 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b3
  have b4 : a 20 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 2 t3 c19 (by decide +kernel)
  have t4 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b4
  have b5 : a 6 ≠ 1 := exclude [0] (edge r24) (a 6) (a 14) 1 d14 c24 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b5
  have b6 : a 7 ≠ 3 := exclude [0] (edge r26) (a 7) (a 15) 3 d15 c26 (by decide +kernel)
  have t6 : a 7 ∈ [0] := remove (a 7) 3 [0,3] d7 b6
  have b7 : a 5 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 2 t3 c16 (by decide +kernel)
  have t7 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_181
