import PartitionData205_227
namespace PartitionCover205_227
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0])
    (d11 : a 11 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d18 : a 18 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 15)=true)
    (c10 : edge r10 (a 1) (a 30)=true)
    (c17 : edge r17 (a 3) (a 11)=true)
    (c18 : edge r18 (a 3) (a 18)=true)
    (c19 : edge r19 (a 3) (a 32)=true)
    (c21 : edge r21 (a 4) (a 6)=true)
    (c22 : edge r22 (a 4) (a 12)=true)
    : a 4 ∈ [0,2] ∧ a 8 ∈ [0,1] ∧ a 15 ∈ [0,2] ∧ a 30 ∈ [0,1] ∧ a 11 ∈ [0,2] ∧ a 18 ∈ [0,2] ∧ a 32 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0,1] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t0 b1
  have b2 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b2
  have b3 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 1 d0 c4 (by decide +kernel)
  have t4 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b4
  have b5 : a 15 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 15) (a 0) 3 d0 c4 (by decide +kernel)
  have t5 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t4 b5
  have b6 : a 30 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 30) (a 1) 2 d1 c10 (by decide +kernel)
  have t6 : a 30 ∈ [0,1,3] := remove (a 30) 2 [0,1,2,3] d30 b6
  have b7 : a 30 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 30) (a 1) 3 d1 c10 (by decide +kernel)
  have t7 : a 30 ∈ [0,1] := remove (a 30) 3 [0,1,3] t6 b7
  have b8 : a 11 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 11) (a 3) 1 d3 c17 (by decide +kernel)
  have t8 : a 11 ∈ [0,2,3] := remove (a 11) 1 [0,1,2,3] d11 b8
  have b9 : a 11 ≠ 3 := exclude [0] (fun u v => edge r17 v u) (a 11) (a 3) 3 d3 c17 (by decide +kernel)
  have t9 : a 11 ∈ [0,2] := remove (a 11) 3 [0,2,3] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 18) (a 3) 1 d3 c18 (by decide +kernel)
  have t10 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b10
  have b11 : a 18 ≠ 3 := exclude [0] (fun u v => edge r18 v u) (a 18) (a 3) 3 d3 c18 (by decide +kernel)
  have t11 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] t10 b11
  have b12 : a 32 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 32) (a 3) 1 d3 c19 (by decide +kernel)
  have t12 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b12
  have b13 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r21 v u) (a 6) (a 4) 1 t1 c21 (by decide +kernel)
  have t13 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b13
  have b14 : a 12 ≠ 2 := exclude [0,2] (fun u v => edge r22 v u) (a 12) (a 4) 2 t1 c22 (by decide +kernel)
  have t14 : a 12 ∈ [0,1,3] := remove (a 12) 2 [0,1,2,3] d12 b14
  have b15 : a 12 ≠ 3 := exclude [0,2] (fun u v => edge r22 v u) (a 12) (a 4) 3 t1 c22 (by decide +kernel)
  have t15 : a 12 ∈ [0,1] := remove (a 12) 3 [0,1,3] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t13 (t15))))))))

theorem chunk1 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d33 : a 33 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d39 : a 39 ∈ [0,1])
    (d11 : a 11 ∈ [0,2])
    (d26 : a 26 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1])
    (d40 : a 40 ∈ [0,1,2,3])
    (c23 : edge r23 (a 4) (a 19)=true)
    (c24 : edge r24 (a 4) (a 33)=true)
    (c29 : edge r29 (a 6) (a 13)=true)
    (c30 : edge r30 (a 6) (a 21)=true)
    (c31 : edge r31 (a 6) (a 35)=true)
    (c33 : edge r33 (a 7) (a 22)=true)
    (c37 : edge r37 (a 8) (a 23)=true)
    (c38 : edge r38 (a 8) (a 36)=true)
    (c47 : edge r47 (a 11) (a 39)=true)
    (c49 : edge r49 (a 12) (a 26)=true)
    (c50 : edge r50 (a 12) (a 40)=true)
    : a 19 ∈ [0] ∧ a 33 ∈ [0] ∧ a 13 ∈ [0,1] ∧ a 21 ∈ [0,1] ∧ a 35 ∈ [0,1] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0] ∧ a 36 ∈ [0] ∧ a 39 ∈ [0] ∧ a 26 ∈ [0,1] ∧ a 40 ∈ [0,2] := by
  have b0 : a 19 ≠ 1 := exclude [0,2] (fun u v => edge r23 v u) (a 19) (a 4) 1 d4 c23 (by decide +kernel)
  have t0 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b0
  have b1 : a 33 ≠ 1 := exclude [0,2] (fun u v => edge r24 v u) (a 33) (a 4) 1 d4 c24 (by decide +kernel)
  have t1 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b1
  have b2 : a 13 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 13) (a 6) 2 d6 c29 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,3] := remove (a 13) 2 [0,1,2,3] d13 b2
  have b3 : a 13 ≠ 3 := exclude [0] (fun u v => edge r29 v u) (a 13) (a 6) 3 d6 c29 (by decide +kernel)
  have t3 : a 13 ∈ [0,1] := remove (a 13) 3 [0,1,3] t2 b3
  have b4 : a 21 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 21) (a 6) 2 d6 c30 (by decide +kernel)
  have t4 : a 21 ∈ [0,1,3] := remove (a 21) 2 [0,1,2,3] d21 b4
  have b5 : a 21 ≠ 3 := exclude [0] (fun u v => edge r30 v u) (a 21) (a 6) 3 d6 c30 (by decide +kernel)
  have t5 : a 21 ∈ [0,1] := remove (a 21) 3 [0,1,3] t4 b5
  have b6 : a 35 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 35) (a 6) 2 d6 c31 (by decide +kernel)
  have t6 : a 35 ∈ [0,1,3] := remove (a 35) 2 [0,1,2,3] d35 b6
  have b7 : a 35 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 35) (a 6) 3 d6 c31 (by decide +kernel)
  have t7 : a 35 ∈ [0,1] := remove (a 35) 3 [0,1,3] t6 b7
  have b8 : a 22 ≠ 1 := exclude [0,1] (fun u v => edge r33 v u) (a 22) (a 7) 1 d7 c33 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b8
  have b9 : a 23 ≠ 1 := exclude [0,1] (fun u v => edge r37 v u) (a 23) (a 8) 1 d8 c37 (by decide +kernel)
  have t9 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b9
  have b10 : a 36 ≠ 1 := exclude [0,1] (fun u v => edge r38 v u) (a 36) (a 8) 1 d8 c38 (by decide +kernel)
  have t10 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b10
  have b11 : a 39 ≠ 1 := exclude [0,2] (fun u v => edge r47 v u) (a 39) (a 11) 1 d11 c47 (by decide +kernel)
  have t11 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b11
  have b12 : a 26 ≠ 2 := exclude [0,1] (fun u v => edge r49 v u) (a 26) (a 12) 2 d12 c49 (by decide +kernel)
  have t12 : a 26 ∈ [0,1,3] := remove (a 26) 2 [0,1,2,3] d26 b12
  have b13 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r49 v u) (a 26) (a 12) 3 d12 c49 (by decide +kernel)
  have t13 : a 26 ∈ [0,1] := remove (a 26) 3 [0,1,3] t12 b13
  have b14 : a 40 ≠ 1 := exclude [0,1] (fun u v => edge r50 v u) (a 40) (a 12) 1 d12 c50 (by decide +kernel)
  have t14 : a 40 ∈ [0,2,3] := remove (a 40) 1 [0,1,2,3] d40 b14
  have b15 : a 40 ≠ 3 := exclude [0,1] (fun u v => edge r50 v u) (a 40) (a 12) 3 d12 c50 (by decide +kernel)
  have t15 : a 40 ∈ [0,2] := remove (a 40) 3 [0,2,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (t15))))))))))

theorem chunk2 (a : Nat → Nat)
    (d43 : a 43 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
    (d20 : a 20 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0])
    (d47 : a 47 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0])
    (d50 : a 50 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3])
    (d51 : a 51 ∈ [0,1,2,3])
    (d52 : a 52 ∈ [0,1])
    (c58 : edge r58 (a 15) (a 43)=true)
    (c69 : edge r69 (a 19) (a 20)=true)
    (c72 : edge r72 (a 19) (a 47)=true)
    (c78 : edge r78 (a 22) (a 28)=true)
    (c79 : edge r79 (a 22) (a 50)=true)
    (c80 : edge r80 (a 23) (a 24)=true)
    (c81 : edge r81 (a 23) (a 25)=true)
    (c84 : edge r84 (a 24) (a 51)=true)
    (c85 : edge r85 (a 25) (a 52)=true)
    : a 43 ∈ [0] ∧ a 20 ∈ [0,2] ∧ a 47 ∈ [0,2] ∧ a 28 ∈ [0,2] ∧ a 50 ∈ [0,1] ∧ a 24 ∈ [0,2] ∧ a 25 ∈ [0,1] ∧ a 51 ∈ [0,2] ∧ a 52 ∈ [0] := by
  have b0 : a 43 ≠ 1 := exclude [0,2] (fun u v => edge r58 v u) (a 43) (a 15) 1 d15 c58 (by decide +kernel)
  have t0 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b0
  have b1 : a 20 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 20) (a 19) 1 d19 c69 (by decide +kernel)
  have t1 : a 20 ∈ [0,2,3] := remove (a 20) 1 [0,1,2,3] d20 b1
  have b2 : a 20 ≠ 3 := exclude [0] (fun u v => edge r69 v u) (a 20) (a 19) 3 d19 c69 (by decide +kernel)
  have t2 : a 20 ∈ [0,2] := remove (a 20) 3 [0,2,3] t1 b2
  have b3 : a 47 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 47) (a 19) 1 d19 c72 (by decide +kernel)
  have t3 : a 47 ∈ [0,2,3] := remove (a 47) 1 [0,1,2,3] d47 b3
  have b4 : a 47 ≠ 3 := exclude [0] (fun u v => edge r72 v u) (a 47) (a 19) 3 d19 c72 (by decide +kernel)
  have t4 : a 47 ∈ [0,2] := remove (a 47) 3 [0,2,3] t3 b4
  have b5 : a 28 ≠ 1 := exclude [0] (fun u v => edge r78 v u) (a 28) (a 22) 1 d22 c78 (by decide +kernel)
  have t5 : a 28 ∈ [0,2,3] := remove (a 28) 1 [0,1,2,3] d28 b5
  have b6 : a 28 ≠ 3 := exclude [0] (fun u v => edge r78 v u) (a 28) (a 22) 3 d22 c78 (by decide +kernel)
  have t6 : a 28 ∈ [0,2] := remove (a 28) 3 [0,2,3] t5 b6
  have b7 : a 50 ≠ 2 := exclude [0] (fun u v => edge r79 v u) (a 50) (a 22) 2 d22 c79 (by decide +kernel)
  have t7 : a 50 ∈ [0,1,3] := remove (a 50) 2 [0,1,2,3] d50 b7
  have b8 : a 50 ≠ 3 := exclude [0] (fun u v => edge r79 v u) (a 50) (a 22) 3 d22 c79 (by decide +kernel)
  have t8 : a 50 ∈ [0,1] := remove (a 50) 3 [0,1,3] t7 b8
  have b9 : a 24 ≠ 1 := exclude [0] (fun u v => edge r80 v u) (a 24) (a 23) 1 d23 c80 (by decide +kernel)
  have t9 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b9
  have b10 : a 24 ≠ 3 := exclude [0] (fun u v => edge r80 v u) (a 24) (a 23) 3 d23 c80 (by decide +kernel)
  have t10 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t9 b10
  have b11 : a 25 ≠ 2 := exclude [0] (fun u v => edge r81 v u) (a 25) (a 23) 2 d23 c81 (by decide +kernel)
  have t11 : a 25 ∈ [0,1,3] := remove (a 25) 2 [0,1,2,3] d25 b11
  have b12 : a 25 ≠ 3 := exclude [0] (fun u v => edge r81 v u) (a 25) (a 23) 3 d23 c81 (by decide +kernel)
  have t12 : a 25 ∈ [0,1] := remove (a 25) 3 [0,1,3] t11 b12
  have b13 : a 51 ≠ 1 := exclude [0,2] (fun u v => edge r84 v u) (a 51) (a 24) 1 t10 c84 (by decide +kernel)
  have t13 : a 51 ∈ [0,2,3] := remove (a 51) 1 [0,1,2,3] d51 b13
  have b14 : a 51 ≠ 3 := exclude [0,2] (fun u v => edge r84 v u) (a 51) (a 24) 3 t10 c84 (by decide +kernel)
  have t14 : a 51 ∈ [0,2] := remove (a 51) 3 [0,2,3] t13 b14
  have b15 : a 52 ≠ 1 := exclude [0,1] (fun u v => edge r85 v u) (a 52) (a 25) 1 t12 c85 (by decide +kernel)
  have t15 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk3 (a : Nat → Nat)
    (d54 : a 54 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d34 : a 34 ∈ [0,1,2,3])
    (d30 : a 30 ∈ [0,1])
    (d37 : a 37 ∈ [0,1,2,3])
    (d44 : a 44 ∈ [0,1,2,3])
    (d38 : a 38 ∈ [0,1,2,3])
    (d36 : a 36 ∈ [0])
    (d42 : a 42 ∈ [0,1,2,3])
    (d39 : a 39 ∈ [0])
    (d53 : a 53 ∈ [0,1,2,3])
    (d45 : a 45 ∈ [0,1,2,3])
    (d43 : a 43 ∈ [0])
    (d55 : a 55 ∈ [0,1,2,3])
    (d51 : a 51 ∈ [0,2])
    (c87 : edge r87 (a 26) (a 54)=true)
    (c96 : edge r96 (a 30) (a 34)=true)
    (c97 : edge r97 (a 30) (a 37)=true)
    (c98 : edge r98 (a 30) (a 44)=true)
    (c113 : edge r113 (a 36) (a 38)=true)
    (c120 : edge r120 (a 39) (a 42)=true)
    (c121 : edge r121 (a 39) (a 53)=true)
    (c127 : edge r127 (a 43) (a 45)=true)
    (c145 : edge r145 (a 51) (a 55)=true)
    : a 54 ∈ [0] ∧ a 34 ∈ [0,2] ∧ a 37 ∈ [0,1] ∧ a 44 ∈ [0,1] ∧ a 38 ∈ [0,1] ∧ a 42 ∈ [0,2] ∧ a 53 ∈ [0,2] ∧ a 45 ∈ [0,2] ∧ a 55 ∈ [0,2,3] := by
  have b0 : a 54 ≠ 1 := exclude [0,1] (fun u v => edge r87 v u) (a 54) (a 26) 1 d26 c87 (by decide +kernel)
  have t0 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b0
  have b1 : a 34 ≠ 1 := exclude [0,1] (fun u v => edge r96 v u) (a 34) (a 30) 1 d30 c96 (by decide +kernel)
  have t1 : a 34 ∈ [0,2,3] := remove (a 34) 1 [0,1,2,3] d34 b1
  have b2 : a 34 ≠ 3 := exclude [0,1] (fun u v => edge r96 v u) (a 34) (a 30) 3 d30 c96 (by decide +kernel)
  have t2 : a 34 ∈ [0,2] := remove (a 34) 3 [0,2,3] t1 b2
  have b3 : a 37 ≠ 2 := exclude [0,1] (fun u v => edge r97 v u) (a 37) (a 30) 2 d30 c97 (by decide +kernel)
  have t3 : a 37 ∈ [0,1,3] := remove (a 37) 2 [0,1,2,3] d37 b3
  have b4 : a 37 ≠ 3 := exclude [0,1] (fun u v => edge r97 v u) (a 37) (a 30) 3 d30 c97 (by decide +kernel)
  have t4 : a 37 ∈ [0,1] := remove (a 37) 3 [0,1,3] t3 b4
  have b5 : a 44 ≠ 2 := exclude [0,1] (fun u v => edge r98 v u) (a 44) (a 30) 2 d30 c98 (by decide +kernel)
  have t5 : a 44 ∈ [0,1,3] := remove (a 44) 2 [0,1,2,3] d44 b5
  have b6 : a 44 ≠ 3 := exclude [0,1] (fun u v => edge r98 v u) (a 44) (a 30) 3 d30 c98 (by decide +kernel)
  have t6 : a 44 ∈ [0,1] := remove (a 44) 3 [0,1,3] t5 b6
  have b7 : a 38 ≠ 2 := exclude [0] (fun u v => edge r113 v u) (a 38) (a 36) 2 d36 c113 (by decide +kernel)
  have t7 : a 38 ∈ [0,1,3] := remove (a 38) 2 [0,1,2,3] d38 b7
  have b8 : a 38 ≠ 3 := exclude [0] (fun u v => edge r113 v u) (a 38) (a 36) 3 d36 c113 (by decide +kernel)
  have t8 : a 38 ∈ [0,1] := remove (a 38) 3 [0,1,3] t7 b8
  have b9 : a 42 ≠ 1 := exclude [0] (fun u v => edge r120 v u) (a 42) (a 39) 1 d39 c120 (by decide +kernel)
  have t9 : a 42 ∈ [0,2,3] := remove (a 42) 1 [0,1,2,3] d42 b9
  have b10 : a 42 ≠ 3 := exclude [0] (fun u v => edge r120 v u) (a 42) (a 39) 3 d39 c120 (by decide +kernel)
  have t10 : a 42 ∈ [0,2] := remove (a 42) 3 [0,2,3] t9 b10
  have b11 : a 53 ≠ 1 := exclude [0] (fun u v => edge r121 v u) (a 53) (a 39) 1 d39 c121 (by decide +kernel)
  have t11 : a 53 ∈ [0,2,3] := remove (a 53) 1 [0,1,2,3] d53 b11
  have b12 : a 53 ≠ 3 := exclude [0] (fun u v => edge r121 v u) (a 53) (a 39) 3 d39 c121 (by decide +kernel)
  have t12 : a 53 ∈ [0,2] := remove (a 53) 3 [0,2,3] t11 b12
  have b13 : a 45 ≠ 1 := exclude [0] (fun u v => edge r127 v u) (a 45) (a 43) 1 d43 c127 (by decide +kernel)
  have t13 : a 45 ∈ [0,2,3] := remove (a 45) 1 [0,1,2,3] d45 b13
  have b14 : a 45 ≠ 3 := exclude [0] (fun u v => edge r127 v u) (a 45) (a 43) 3 d43 c127 (by decide +kernel)
  have t14 : a 45 ∈ [0,2] := remove (a 45) 3 [0,2,3] t13 b14
  have b15 : a 55 ≠ 1 := exclude [0,2] (fun u v => edge r145 v u) (a 55) (a 51) 1 d51 c145 (by decide +kernel)
  have t15 : a 55 ∈ [0,2,3] := remove (a 55) 1 [0,1,2,3] d55 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_227
