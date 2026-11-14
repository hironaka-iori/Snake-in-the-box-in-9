import PartitionData205_231
namespace PartitionCover205_231
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1])
    (d3 : a 3 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0,1])
    (d14 : a 14 ∈ [0,1,2,3])
    (d36 : a 36 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c17 : edge r17 (a 3) (a 11)=true)
    (c19 : edge r19 (a 4) (a 6)=true)
    (c20 : edge r20 (a 4) (a 12)=true)
    (c21 : edge r21 (a 4) (a 19)=true)
    (c22 : edge r22 (a 4) (a 34)=true)
    (c28 : edge r28 (a 6) (a 14)=true)
    (c30 : edge r30 (a 6) (a 36)=true)
    (c37 : edge r37 (a 8) (a 23)=true)
    (c38 : edge r38 (a 8) (a 38)=true)
    : a 4 ∈ [0,2] ∧ a 8 ∈ [0,2] ∧ a 11 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0,2] ∧ a 19 ∈ [0,2] ∧ a 34 ∈ [0] ∧ a 14 ∈ [0,2] ∧ a 36 ∈ [0] ∧ a 23 ∈ [0] ∧ a 38 ∈ [0] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t0 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b0
  have b1 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b2
  have b3 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t2 b3
  have b4 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r17 v u) (a 11) (a 3) 1 d3 c17 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b4
  have b5 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r19 v u) (a 6) (a 4) 1 t1 c19 (by decide +kernel)
  have t5 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b5
  have b6 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r20 v u) (a 12) (a 4) 1 t1 c20 (by decide +kernel)
  have t6 : a 12 ∈ [0,2,3] := remove (a 12) 1 [0,1,2,3] d12 b6
  have b7 : a 12 ≠ 3 := exclude [0,2] (fun u v => edge r20 v u) (a 12) (a 4) 3 t1 c20 (by decide +kernel)
  have t7 : a 12 ∈ [0,2] := remove (a 12) 3 [0,2,3] t6 b7
  have b8 : a 19 ≠ 1 := exclude [0,2] (fun u v => edge r21 v u) (a 19) (a 4) 1 t1 c21 (by decide +kernel)
  have t8 : a 19 ∈ [0,2,3] := remove (a 19) 1 [0,1,2,3] d19 b8
  have b9 : a 19 ≠ 3 := exclude [0,2] (fun u v => edge r21 v u) (a 19) (a 4) 3 t1 c21 (by decide +kernel)
  have t9 : a 19 ∈ [0,2] := remove (a 19) 3 [0,2,3] t8 b9
  have b10 : a 34 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 34) (a 4) 1 t1 c22 (by decide +kernel)
  have t10 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b10
  have b11 : a 14 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 14) (a 6) 1 t5 c28 (by decide +kernel)
  have t11 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b11
  have b12 : a 14 ≠ 3 := exclude [0] (fun u v => edge r28 v u) (a 14) (a 6) 3 t5 c28 (by decide +kernel)
  have t12 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t11 b12
  have b13 : a 36 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 36) (a 6) 1 t5 c30 (by decide +kernel)
  have t13 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b13
  have b14 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r37 v u) (a 23) (a 8) 1 t3 c37 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b14
  have b15 : a 38 ≠ 1 := exclude [0,2] (fun u v => edge r38 v u) (a 38) (a 8) 1 t3 c38 (by decide +kernel)
  have t15 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))))

theorem chunk1 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3])
    (d41 : a 41 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d27 : a 27 ∈ [0,1,2,3])
    (d42 : a 42 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,2])
    (d20 : a 20 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,2,3])
    (c47 : edge r47 (a 11) (a 15)=true)
    (c48 : edge r48 (a 11) (a 26)=true)
    (c49 : edge r49 (a 11) (a 41)=true)
    (c50 : edge r50 (a 12) (a 13)=true)
    (c52 : edge r52 (a 12) (a 27)=true)
    (c53 : edge r53 (a 12) (a 42)=true)
    (c58 : edge r58 (a 14) (a 29)=true)
    (c66 : edge r66 (a 17) (a 20)=true)
    (c67 : edge r67 (a 17) (a 24)=true)
    : a 15 ∈ [0,2] ∧ a 26 ∈ [0,2] ∧ a 41 ∈ [0,1] ∧ a 13 ∈ [0] ∧ a 27 ∈ [0,1] ∧ a 42 ∈ [0,2] ∧ a 29 ∈ [0,1] ∧ a 20 ∈ [0] ∧ a 24 ∈ [0,1] := by
  have b0 : a 15 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 15) (a 11) 1 d11 c47 (by decide +kernel)
  have t0 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b0
  have b1 : a 15 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 15) (a 11) 3 d11 c47 (by decide +kernel)
  have t1 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t0 b1
  have b2 : a 26 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 26) (a 11) 1 d11 c48 (by decide +kernel)
  have t2 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b2
  have b3 : a 26 ≠ 3 := exclude [0] (fun u v => edge r48 v u) (a 26) (a 11) 3 d11 c48 (by decide +kernel)
  have t3 : a 26 ∈ [0,2] := remove (a 26) 3 [0,2,3] t2 b3
  have b4 : a 41 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 41) (a 11) 2 d11 c49 (by decide +kernel)
  have t4 : a 41 ∈ [0,1,3] := remove (a 41) 2 [0,1,2,3] d41 b4
  have b5 : a 41 ≠ 3 := exclude [0] (fun u v => edge r49 v u) (a 41) (a 11) 3 d11 c49 (by decide +kernel)
  have t5 : a 41 ∈ [0,1] := remove (a 41) 3 [0,1,3] t4 b5
  have b6 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r50 v u) (a 13) (a 12) 1 d12 c50 (by decide +kernel)
  have t6 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b6
  have b7 : a 27 ≠ 2 := exclude [0,2] (fun u v => edge r52 v u) (a 27) (a 12) 2 d12 c52 (by decide +kernel)
  have t7 : a 27 ∈ [0,1,3] := remove (a 27) 2 [0,1,2,3] d27 b7
  have b8 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r52 v u) (a 27) (a 12) 3 d12 c52 (by decide +kernel)
  have t8 : a 27 ∈ [0,1] := remove (a 27) 3 [0,1,3] t7 b8
  have b9 : a 42 ≠ 1 := exclude [0,2] (fun u v => edge r53 v u) (a 42) (a 12) 1 d12 c53 (by decide +kernel)
  have t9 : a 42 ∈ [0,2,3] := remove (a 42) 1 [0,1,2,3] d42 b9
  have b10 : a 42 ≠ 3 := exclude [0,2] (fun u v => edge r53 v u) (a 42) (a 12) 3 d12 c53 (by decide +kernel)
  have t10 : a 42 ∈ [0,2] := remove (a 42) 3 [0,2,3] t9 b10
  have b11 : a 29 ≠ 2 := exclude [0,2] (fun u v => edge r58 v u) (a 29) (a 14) 2 d14 c58 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,3] := remove (a 29) 2 [0,1,2,3] d29 b11
  have b12 : a 29 ≠ 3 := exclude [0,2] (fun u v => edge r58 v u) (a 29) (a 14) 3 d14 c58 (by decide +kernel)
  have t12 : a 29 ∈ [0,1] := remove (a 29) 3 [0,1,3] t11 b12
  have b13 : a 20 ≠ 1 := exclude [0,1] (fun u v => edge r66 v u) (a 20) (a 17) 1 d17 c66 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b13
  have b14 : a 24 ≠ 2 := exclude [0,1] (fun u v => edge r67 v u) (a 24) (a 17) 2 d17 c67 (by decide +kernel)
  have t14 : a 24 ∈ [0,1,3] := remove (a 24) 2 [0,1,2,3] d24 b14
  have b15 : a 24 ≠ 3 := exclude [0,1] (fun u v => edge r67 v u) (a 24) (a 17) 3 d17 c67 (by decide +kernel)
  have t15 : a 24 ∈ [0,1] := remove (a 24) 3 [0,1,3] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t13 (t15))))))))

theorem chunk2 (a : Nat → Nat)
    (d46 : a 46 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1])
    (d49 : a 49 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,2])
    (d22 : a 22 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0])
    (d52 : a 52 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d54 : a 54 ∈ [0,1,2,3])
    (d24 : a 24 ∈ [0,1])
    (d56 : a 56 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,2])
    (d58 : a 58 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1])
    (d35 : a 35 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1])
    (c68 : edge r68 (a 17) (a 46)=true)
    (c75 : edge r75 (a 19) (a 49)=true)
    (c76 : edge r76 (a 20) (a 22)=true)
    (c83 : edge r83 (a 22) (a 52)=true)
    (c85 : edge r85 (a 23) (a 25)=true)
    (c90 : edge r90 (a 24) (a 54)=true)
    (c95 : edge r95 (a 26) (a 56)=true)
    (c101 : edge r101 (a 29) (a 58)=true)
    (c108 : edge r108 (a 32) (a 35)=true)
    : a 46 ∈ [0,1] ∧ a 49 ∈ [0,1] ∧ a 22 ∈ [0,1] ∧ a 52 ∈ [0,1] ∧ a 25 ∈ [0] ∧ a 54 ∈ [0,2] ∧ a 56 ∈ [0,2] ∧ a 58 ∈ [0,1] ∧ a 35 ∈ [0,2,3] := by
  have b0 : a 46 ≠ 2 := exclude [0,1] (fun u v => edge r68 v u) (a 46) (a 17) 2 d17 c68 (by decide +kernel)
  have t0 : a 46 ∈ [0,1,3] := remove (a 46) 2 [0,1,2,3] d46 b0
  have b1 : a 46 ≠ 3 := exclude [0,1] (fun u v => edge r68 v u) (a 46) (a 17) 3 d17 c68 (by decide +kernel)
  have t1 : a 46 ∈ [0,1] := remove (a 46) 3 [0,1,3] t0 b1
  have b2 : a 49 ≠ 2 := exclude [0,2] (fun u v => edge r75 v u) (a 49) (a 19) 2 d19 c75 (by decide +kernel)
  have t2 : a 49 ∈ [0,1,3] := remove (a 49) 2 [0,1,2,3] d49 b2
  have b3 : a 49 ≠ 3 := exclude [0,2] (fun u v => edge r75 v u) (a 49) (a 19) 3 d19 c75 (by decide +kernel)
  have t3 : a 49 ∈ [0,1] := remove (a 49) 3 [0,1,3] t2 b3
  have b4 : a 22 ≠ 2 := exclude [0] (fun u v => edge r76 v u) (a 22) (a 20) 2 d20 c76 (by decide +kernel)
  have t4 : a 22 ∈ [0,1,3] := remove (a 22) 2 [0,1,2,3] d22 b4
  have b5 : a 22 ≠ 3 := exclude [0] (fun u v => edge r76 v u) (a 22) (a 20) 3 d20 c76 (by decide +kernel)
  have t5 : a 22 ∈ [0,1] := remove (a 22) 3 [0,1,3] t4 b5
  have b6 : a 52 ≠ 2 := exclude [0,1] (fun u v => edge r83 v u) (a 52) (a 22) 2 t5 c83 (by decide +kernel)
  have t6 : a 52 ∈ [0,1,3] := remove (a 52) 2 [0,1,2,3] d52 b6
  have b7 : a 52 ≠ 3 := exclude [0,1] (fun u v => edge r83 v u) (a 52) (a 22) 3 t5 c83 (by decide +kernel)
  have t7 : a 52 ∈ [0,1] := remove (a 52) 3 [0,1,3] t6 b7
  have b8 : a 25 ≠ 1 := exclude [0] (fun u v => edge r85 v u) (a 25) (a 23) 1 d23 c85 (by decide +kernel)
  have t8 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b8
  have b9 : a 54 ≠ 1 := exclude [0,1] (fun u v => edge r90 v u) (a 54) (a 24) 1 d24 c90 (by decide +kernel)
  have t9 : a 54 ∈ [0,2,3] := remove (a 54) 1 [0,1,2,3] d54 b9
  have b10 : a 54 ≠ 3 := exclude [0,1] (fun u v => edge r90 v u) (a 54) (a 24) 3 d24 c90 (by decide +kernel)
  have t10 : a 54 ∈ [0,2] := remove (a 54) 3 [0,2,3] t9 b10
  have b11 : a 56 ≠ 1 := exclude [0,2] (fun u v => edge r95 v u) (a 56) (a 26) 1 d26 c95 (by decide +kernel)
  have t11 : a 56 ∈ [0,2,3] := remove (a 56) 1 [0,1,2,3] d56 b11
  have b12 : a 56 ≠ 3 := exclude [0,2] (fun u v => edge r95 v u) (a 56) (a 26) 3 d26 c95 (by decide +kernel)
  have t12 : a 56 ∈ [0,2] := remove (a 56) 3 [0,2,3] t11 b12
  have b13 : a 58 ≠ 2 := exclude [0,1] (fun u v => edge r101 v u) (a 58) (a 29) 2 d29 c101 (by decide +kernel)
  have t13 : a 58 ∈ [0,1,3] := remove (a 58) 2 [0,1,2,3] d58 b13
  have b14 : a 58 ≠ 3 := exclude [0,1] (fun u v => edge r101 v u) (a 58) (a 29) 3 d29 c101 (by decide +kernel)
  have t14 : a 58 ∈ [0,1] := remove (a 58) 3 [0,1,3] t13 b14
  have b15 : a 35 ≠ 1 := exclude [0,1] (fun u v => edge r108 v u) (a 35) (a 32) 1 d32 c108 (by decide +kernel)
  have t15 : a 35 ∈ [0,2,3] := remove (a 35) 1 [0,1,2,3] d35 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk3 (a : Nat → Nat)
    (d35 : a 35 ∈ [0,2,3])
    (d32 : a 32 ∈ [0,1])
    (d39 : a 39 ∈ [0,1,2,3])
    (d33 : a 33 ∈ [0,1,2,3])
    (d36 : a 36 ∈ [0])
    (d40 : a 40 ∈ [0,1,2,3])
    (d47 : a 47 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d59 : a 59 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d57 : a 57 ∈ [0,1,2,3])
    (d54 : a 54 ∈ [0,2])
    (c108 : edge r108 (a 32) (a 35)=true)
    (c109 : edge r109 (a 32) (a 39)=true)
    (c111 : edge r111 (a 33) (a 36)=true)
    (c112 : edge r112 (a 33) (a 40)=true)
    (c113 : edge r113 (a 33) (a 47)=true)
    (c122 : edge r122 (a 36) (a 51)=true)
    (c140 : edge r140 (a 45) (a 46)=true)
    (c158 : edge r158 (a 52) (a 59)=true)
    (c162 : edge r162 (a 54) (a 57)=true)
    : a 35 ∈ [0,2] ∧ a 39 ∈ [0,2] ∧ a 33 ∈ [0,2] ∧ a 40 ∈ [0,2] ∧ a 47 ∈ [0] ∧ a 51 ∈ [0] ∧ a 45 ∈ [0] ∧ a 59 ∈ [0] ∧ a 57 ∈ [0,2] := by
  have b0 : a 35 ≠ 3 := exclude [0,1] (fun u v => edge r108 v u) (a 35) (a 32) 3 d32 c108 (by decide +kernel)
  have t0 : a 35 ∈ [0,2] := remove (a 35) 3 [0,2,3] d35 b0
  have b1 : a 39 ≠ 1 := exclude [0,1] (fun u v => edge r109 v u) (a 39) (a 32) 1 d32 c109 (by decide +kernel)
  have t1 : a 39 ∈ [0,2,3] := remove (a 39) 1 [0,1,2,3] d39 b1
  have b2 : a 39 ≠ 3 := exclude [0,1] (fun u v => edge r109 v u) (a 39) (a 32) 3 d32 c109 (by decide +kernel)
  have t2 : a 39 ∈ [0,2] := remove (a 39) 3 [0,2,3] t1 b2
  have b3 : a 33 ≠ 1 := exclude [0] (edge r111) (a 33) (a 36) 1 d36 c111 (by decide +kernel)
  have t3 : a 33 ∈ [0,2,3] := remove (a 33) 1 [0,1,2,3] d33 b3
  have b4 : a 33 ≠ 3 := exclude [0] (edge r111) (a 33) (a 36) 3 d36 c111 (by decide +kernel)
  have t4 : a 33 ∈ [0,2] := remove (a 33) 3 [0,2,3] t3 b4
  have b5 : a 40 ≠ 1 := exclude [0,2] (fun u v => edge r112 v u) (a 40) (a 33) 1 t4 c112 (by decide +kernel)
  have t5 : a 40 ∈ [0,2,3] := remove (a 40) 1 [0,1,2,3] d40 b5
  have b6 : a 40 ≠ 3 := exclude [0,2] (fun u v => edge r112 v u) (a 40) (a 33) 3 t4 c112 (by decide +kernel)
  have t6 : a 40 ∈ [0,2] := remove (a 40) 3 [0,2,3] t5 b6
  have b7 : a 47 ≠ 1 := exclude [0,2] (fun u v => edge r113 v u) (a 47) (a 33) 1 t4 c113 (by decide +kernel)
  have t7 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b7
  have b8 : a 51 ≠ 1 := exclude [0] (fun u v => edge r122 v u) (a 51) (a 36) 1 d36 c122 (by decide +kernel)
  have t8 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b8
  have b9 : a 45 ≠ 1 := exclude [0,1] (edge r140) (a 45) (a 46) 1 d46 c140 (by decide +kernel)
  have t9 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b9
  have b10 : a 59 ≠ 1 := exclude [0,1] (fun u v => edge r158 v u) (a 59) (a 52) 1 d52 c158 (by decide +kernel)
  have t10 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b10
  have b11 : a 57 ≠ 1 := exclude [0,2] (fun u v => edge r162 v u) (a 57) (a 54) 1 d54 c162 (by decide +kernel)
  have t11 : a 57 ∈ [0,2,3] := remove (a 57) 1 [0,1,2,3] d57 b11
  have b12 : a 57 ≠ 3 := exclude [0,2] (fun u v => edge r162 v u) (a 57) (a 54) 3 d54 c162 (by decide +kernel)
  have t12 : a 57 ∈ [0,2] := remove (a 57) 3 [0,2,3] t11 b12
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t12))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_231
