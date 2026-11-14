import PartitionData205_228
namespace PartitionCover205_228
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1])
    (d3 : a 3 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1])
    (d28 : a 28 ∈ [0,1,2,3])
    (d51 : a 51 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d54 : a 54 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1])
    (d26 : a 26 ∈ [0,1,2,3])
    (c16 : edge r16 (a 3) (a 17)=true)
    (c34 : edge r34 (a 8) (a 23)=true)
    (c61 : edge r61 (a 17) (a 21)=true)
    (c62 : edge r62 (a 17) (a 25)=true)
    (c64 : edge r64 (a 18) (a 19)=true)
    (c66 : edge r66 (a 18) (a 26)=true)
    (c68 : edge r68 (a 19) (a 21)=true)
    (c73 : edge r73 (a 21) (a 28)=true)
    (c80 : edge r80 (a 23) (a 51)=true)
    (c126 : edge r126 (a 43) (a 51)=true)
    (c141 : edge r141 (a 51) (a 54)=true)
    : a 17 ∈ [0] ∧ a 23 ∈ [0,2] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0,2] ∧ a 19 ∈ [0] ∧ a 28 ∈ [0,2] ∧ a 51 ∈ [0] ∧ a 43 ∈ [0] ∧ a 54 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 26 ∈ [0,1] := by
  have b0 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r16 v u) (a 17) (a 3) 1 d3 c16 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b0
  have b1 : a 23 ≠ 1 := exclude [0,1] (fun u v => edge r34 v u) (a 23) (a 8) 1 d8 c34 (by decide +kernel)
  have t1 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b1
  have b2 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r34 v u) (a 23) (a 8) 3 d8 c34 (by decide +kernel)
  have t2 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t1 b2
  have b3 : a 21 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 21) (a 17) 1 t0 c61 (by decide +kernel)
  have t3 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b3
  have b4 : a 25 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 25) (a 17) 1 t0 c62 (by decide +kernel)
  have t4 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b4
  have b5 : a 25 ≠ 3 := exclude [0] (fun u v => edge r62 v u) (a 25) (a 17) 3 t0 c62 (by decide +kernel)
  have t5 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t4 b5
  have b6 : a 19 ≠ 1 := exclude [0] (edge r68) (a 19) (a 21) 1 t3 c68 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b6
  have b7 : a 28 ≠ 1 := exclude [0] (fun u v => edge r73 v u) (a 28) (a 21) 1 t3 c73 (by decide +kernel)
  have t7 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b7
  have b8 : a 28 ≠ 3 := exclude [0] (fun u v => edge r73 v u) (a 28) (a 21) 3 t3 c73 (by decide +kernel)
  have t8 : a 28 ∈ [0,2] := remove (a 28) 3 [0,2,3] t7 b8
  have b9 : a 51 ≠ 1 := exclude [0,2] (fun u v => edge r80 v u) (a 51) (a 23) 1 t2 c80 (by decide +kernel)
  have t9 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b9
  have b10 : a 43 ≠ 1 := exclude [0] (edge r126) (a 43) (a 51) 1 t9 c126 (by decide +kernel)
  have t10 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b10
  have b11 : a 54 ≠ 1 := exclude [0] (fun u v => edge r141 v u) (a 54) (a 51) 1 t9 c141 (by decide +kernel)
  have t11 : a 54 ∈ [0,2,3] := remove (a 54) 1 [0,1,2,3] d54 b11
  have b12 : a 54 ≠ 3 := exclude [0] (fun u v => edge r141 v u) (a 54) (a 51) 3 t9 c141 (by decide +kernel)
  have t12 : a 54 ∈ [0,2] := remove (a 54) 3 [0,2,3] t11 b12
  have b13 : a 18 ≠ 1 := exclude [0] (edge r64) (a 18) (a 19) 1 t6 c64 (by decide +kernel)
  have t13 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b13
  have b14 : a 26 ≠ 2 := exclude [0] (fun u v => edge r66 v u) (a 26) (a 18) 2 t13 c66 (by decide +kernel)
  have t14 : a 26 ∈ [0,1,3] := remove (a 26) 2 [0,1,2,3] d26 b14
  have b15 : a 26 ≠ 3 := exclude [0] (fun u v => edge r66 v u) (a 26) (a 18) 3 t13 c66 (by decide +kernel)
  have t15 : a 26 ∈ [0,1] := remove (a 26) 3 [0,1,3] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))))))))

theorem chunk1 (a : Nat → Nat)
    (d42 : a 42 ∈ [0,1])
    (d43 : a 43 ∈ [0])
    (d44 : a 44 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d55 : a 55 ∈ [0,1,2,3])
    (c120 : edge r120 (a 42) (a 43)=true)
    (c121 : edge r121 (a 42) (a 44)=true)
    (c128 : edge r128 (a 44) (a 48)=true)
    (c137 : edge r137 (a 48) (a 55)=true)
    : a 42 ∈ [0] ∧ a 44 ∈ [0] ∧ a 48 ∈ [0] ∧ a 55 ∈ [0,1] := by
  have b0 : a 42 ≠ 1 := exclude [0] (edge r120) (a 42) (a 43) 1 d43 c120 (by decide +kernel)
  have t0 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b0
  have b1 : a 44 ≠ 1 := exclude [0] (fun u v => edge r121 v u) (a 44) (a 42) 1 t0 c121 (by decide +kernel)
  have t1 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b1
  have b2 : a 48 ≠ 1 := exclude [0] (fun u v => edge r128 v u) (a 48) (a 44) 1 t1 c128 (by decide +kernel)
  have t2 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b2
  have b3 : a 55 ≠ 2 := exclude [0] (fun u v => edge r137 v u) (a 55) (a 48) 2 t2 c137 (by decide +kernel)
  have t3 : a 55 ∈ [0,1,3] := remove (a 55) 2 [0,1,2,3] d55 b3
  have b4 : a 55 ≠ 3 := exclude [0] (fun u v => edge r137 v u) (a 55) (a 48) 3 t2 c137 (by decide +kernel)
  have t4 : a 55 ∈ [0,1] := remove (a 55) 3 [0,1,3] t3 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (t4)))

theorem chunk2 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d34 : a 34 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d37 : a 37 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d28 : a 28 ∈ [0,2])
    (d41 : a 41 ∈ [0,1])
    (c15 : edge r15 (a 3) (a 7)=true)
    (c22 : edge r22 (a 5) (a 7)=true)
    (c23 : edge r23 (a 5) (a 11)=true)
    (c26 : edge r26 (a 6) (a 7)=true)
    (c27 : edge r27 (a 6) (a 12)=true)
    (c28 : edge r28 (a 6) (a 20)=true)
    (c29 : edge r29 (a 6) (a 34)=true)
    (c30 : edge r30 (a 7) (a 13)=true)
    (c33 : edge r33 (a 8) (a 11)=true)
    (c34 : edge r34 (a 8) (a 23)=true)
    (c35 : edge r35 (a 8) (a 37)=true)
    (c39 : edge r39 (a 10) (a 11)=true)
    (c41 : edge r41 (a 10) (a 26)=true)
    (c45 : edge r45 (a 12) (a 27)=true)
    (c46 : edge r46 (a 13) (a 28)=true)
    (c47 : edge r47 (a 13) (a 41)=true)
    : a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 11 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 34 ∈ [0] ∧ a 13 ∈ [0] ∧ a 8 ∈ [0] ∧ a 23 ∈ [0] ∧ a 37 ∈ [0] ∧ a 10 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 41 ∈ [0] := by
  have b0 : a 7 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 3) 1 d3 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b0
  have b1 : a 5 ≠ 1 := exclude [0] (edge r22) (a 5) (a 7) 1 t0 c22 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 11 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 11) (a 5) 1 t1 c23 (by decide +kernel)
  have t2 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b2
  have b3 : a 6 ≠ 1 := exclude [0] (edge r26) (a 6) (a 7) 1 t0 c26 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b3
  have b4 : a 12 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 12) (a 6) 1 t3 c27 (by decide +kernel)
  have t4 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b4
  have b5 : a 20 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 20) (a 6) 1 t3 c28 (by decide +kernel)
  have t5 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b5
  have b6 : a 34 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 34) (a 6) 1 t3 c29 (by decide +kernel)
  have t6 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b6
  have b7 : a 13 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 13) (a 7) 1 t0 c30 (by decide +kernel)
  have t7 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b7
  have b8 : a 8 ≠ 1 := exclude [0] (edge r33) (a 8) (a 11) 1 t2 c33 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b8
  have b9 : a 23 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 23) (a 8) 2 t8 c34 (by decide +kernel)
  have t9 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b9
  have b10 : a 37 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 37) (a 8) 1 t8 c35 (by decide +kernel)
  have t10 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b10
  have b11 : a 10 ≠ 1 := exclude [0] (edge r39) (a 10) (a 11) 1 t2 c39 (by decide +kernel)
  have t11 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b11
  have b12 : a 26 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 26) (a 10) 1 t11 c41 (by decide +kernel)
  have t12 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b12
  have b13 : a 27 ≠ 1 := exclude [0] (fun u v => edge r45 v u) (a 27) (a 12) 1 t4 c45 (by decide +kernel)
  have t13 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b13
  have b14 : a 28 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 28) (a 13) 2 t7 c46 (by decide +kernel)
  have t14 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b14
  have b15 : a 41 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 41) (a 13) 1 t7 c47 (by decide +kernel)
  have t15 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk3 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d50 : a 50 ∈ [0,1])
    (d25 : a 25 ∈ [0,2])
    (d52 : a 52 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d55 : a 55 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d37 : a 37 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d34 : a 34 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d54 : a 54 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d5 : a 5 ∈ [0])
    (c17 : edge r17 (a 4) (a 5)=true)
    (c55 : edge r55 (a 15) (a 23)=true)
    (c58 : edge r58 (a 16) (a 20)=true)
    (c59 : edge r59 (a 16) (a 24)=true)
    (c75 : edge r75 (a 22) (a 23)=true)
    (c78 : edge r78 (a 22) (a 50)=true)
    (c79 : edge r79 (a 23) (a 25)=true)
    (c84 : edge r84 (a 25) (a 52)=true)
    (c86 : edge r86 (a 26) (a 53)=true)
    (c88 : edge r88 (a 27) (a 55)=true)
    (c95 : edge r95 (a 30) (a 37)=true)
    (c97 : edge r97 (a 31) (a 34)=true)
    (c114 : edge r114 (a 37) (a 39)=true)
    (c130 : edge r130 (a 45) (a 52)=true)
    (c133 : edge r133 (a 46) (a 53)=true)
    (c142 : edge r142 (a 53) (a 54)=true)
    : a 15 ∈ [0] ∧ a 16 ∈ [0] ∧ a 24 ∈ [0] ∧ a 22 ∈ [0] ∧ a 50 ∈ [0] ∧ a 25 ∈ [0] ∧ a 52 ∈ [0] ∧ a 53 ∈ [0] ∧ a 55 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 39 ∈ [0] ∧ a 45 ∈ [0] ∧ a 46 ∈ [0] ∧ a 54 ∈ [0] ∧ a 4 ∈ [0] := by
  have b0 : a 15 ≠ 1 := exclude [0] (edge r55) (a 15) (a 23) 1 d23 c55 (by decide +kernel)
  have t0 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b0
  have b1 : a 16 ≠ 1 := exclude [0] (edge r58) (a 16) (a 20) 1 d20 c58 (by decide +kernel)
  have t1 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b1
  have b2 : a 24 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 24) (a 16) 1 t1 c59 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b2
  have b3 : a 22 ≠ 1 := exclude [0] (edge r75) (a 22) (a 23) 1 d23 c75 (by decide +kernel)
  have t3 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b3
  have b4 : a 50 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 50) (a 22) 1 t3 c78 (by decide +kernel)
  have t4 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b4
  have b5 : a 25 ≠ 2 := exclude [0] (fun u v => edge r79 v u) (a 25) (a 23) 2 d23 c79 (by decide +kernel)
  have t5 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b5
  have b6 : a 52 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 52) (a 25) 1 t5 c84 (by decide +kernel)
  have t6 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b6
  have b7 : a 53 ≠ 1 := exclude [0] (fun u v => edge r86 v u) (a 53) (a 26) 1 d26 c86 (by decide +kernel)
  have t7 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b7
  have b8 : a 55 ≠ 1 := exclude [0] (fun u v => edge r88 v u) (a 55) (a 27) 1 d27 c88 (by decide +kernel)
  have t8 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b8
  have b9 : a 30 ≠ 1 := exclude [0] (edge r95) (a 30) (a 37) 1 d37 c95 (by decide +kernel)
  have t9 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b9
  have b10 : a 31 ≠ 1 := exclude [0] (edge r97) (a 31) (a 34) 1 d34 c97 (by decide +kernel)
  have t10 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b10
  have b11 : a 39 ≠ 1 := exclude [0] (fun u v => edge r114 v u) (a 39) (a 37) 1 d37 c114 (by decide +kernel)
  have t11 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b11
  have b12 : a 45 ≠ 1 := exclude [0] (edge r130) (a 45) (a 52) 1 t6 c130 (by decide +kernel)
  have t12 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b12
  have b13 : a 46 ≠ 1 := exclude [0] (edge r133) (a 46) (a 53) 1 t7 c133 (by decide +kernel)
  have t13 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b13
  have b14 : a 54 ≠ 2 := exclude [0] (fun u v => edge r142 v u) (a 54) (a 53) 2 t7 c142 (by decide +kernel)
  have t14 : a 54 ∈ [0] := remove (a 54) 2 [0,2] d54 b14
  have b15 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 5) 1 d5 c17 (by decide +kernel)
  have t15 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_228
