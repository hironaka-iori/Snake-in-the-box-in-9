import PartitionData205_223
namespace PartitionCover205_223
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1,2,3])
    (d8 : a 8 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1,2,3])
    (d10 : a 10 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0])
    (d18 : a 18 ∈ [0,1])
    (d33 : a 33 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2,3])
    (d37 : a 37 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c14 : edge r14 (a 2) (a 32)=true)
    (c16 : edge r16 (a 3) (a 10)=true)
    (c20 : edge r20 (a 4) (a 18)=true)
    (c21 : edge r21 (a 4) (a 33)=true)
    (c35 : edge r35 (a 8) (a 22)=true)
    (c36 : edge r36 (a 8) (a 37)=true)
    (c42 : edge r42 (a 10) (a 25)=true)
    : a 2 ∈ [0,2] ∧ a 4 ∈ [0,2] ∧ a 8 ∈ [0,1] ∧ a 32 ∈ [0,2] ∧ a 10 ∈ [0,1] ∧ a 18 ∈ [0] ∧ a 33 ∈ [0] ∧ a 22 ∈ [0,2] ∧ a 37 ∈ [0] ∧ a 25 ∈ [0,2,3] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t2 : a 4 ∈ [0,2,3] := remove (a 4) 1 [0,1,2,3] d4 b2
  have b3 : a 4 ≠ 3 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 3 d0 c2 (by decide +kernel)
  have t3 : a 4 ∈ [0,2] := remove (a 4) 3 [0,2,3] t2 b3
  have b4 : a 8 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 2 d0 c3 (by decide +kernel)
  have t4 : a 8 ∈ [0,1,3] := remove (a 8) 2 [0,1,2,3] d8 b4
  have b5 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t5 : a 8 ∈ [0,1] := remove (a 8) 3 [0,1,3] t4 b5
  have b6 : a 32 ≠ 1 := exclude [0,2] (fun u v => edge r14 v u) (a 32) (a 2) 1 t1 c14 (by decide +kernel)
  have t6 : a 32 ∈ [0,2,3] := remove (a 32) 1 [0,1,2,3] d32 b6
  have b7 : a 32 ≠ 3 := exclude [0,2] (fun u v => edge r14 v u) (a 32) (a 2) 3 t1 c14 (by decide +kernel)
  have t7 : a 32 ∈ [0,2] := remove (a 32) 3 [0,2,3] t6 b7
  have b8 : a 10 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 10) (a 3) 2 d3 c16 (by decide +kernel)
  have t8 : a 10 ∈ [0,1,3] := remove (a 10) 2 [0,1,2,3] d10 b8
  have b9 : a 10 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 10) (a 3) 3 d3 c16 (by decide +kernel)
  have t9 : a 10 ∈ [0,1] := remove (a 10) 3 [0,1,3] t8 b9
  have b10 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r20 v u) (a 18) (a 4) 1 t3 c20 (by decide +kernel)
  have t10 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b10
  have b11 : a 33 ≠ 1 := exclude [0,2] (fun u v => edge r21 v u) (a 33) (a 4) 1 t3 c21 (by decide +kernel)
  have t11 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b11
  have b12 : a 22 ≠ 1 := exclude [0,1] (fun u v => edge r35 v u) (a 22) (a 8) 1 t5 c35 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b12
  have b13 : a 22 ≠ 3 := exclude [0,1] (fun u v => edge r35 v u) (a 22) (a 8) 3 t5 c35 (by decide +kernel)
  have t13 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t12 b13
  have b14 : a 37 ≠ 1 := exclude [0,1] (fun u v => edge r36 v u) (a 37) (a 8) 1 t5 c36 (by decide +kernel)
  have t14 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b14
  have b15 : a 25 ≠ 1 := exclude [0,1] (fun u v => edge r42 v u) (a 25) (a 10) 1 t9 c42 (by decide +kernel)
  have t15 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (And.intro t14 (t15)))))))))

theorem chunk1 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,2,3])
    (d10 : a 10 ∈ [0,1])
    (d40 : a 40 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1])
    (d41 : a 41 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d45 : a 45 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d49 : a 49 ∈ [0,1,2,3])
    (c42 : edge r42 (a 10) (a 25)=true)
    (c43 : edge r43 (a 10) (a 40)=true)
    (c46 : edge r46 (a 11) (a 26)=true)
    (c47 : edge r47 (a 11) (a 41)=true)
    (c52 : edge r52 (a 13) (a 28)=true)
    (c60 : edge r60 (a 16) (a 19)=true)
    (c61 : edge r61 (a 16) (a 23)=true)
    (c62 : edge r62 (a 16) (a 45)=true)
    (c67 : edge r67 (a 18) (a 20)=true)
    (c72 : edge r72 (a 19) (a 49)=true)
    : a 25 ∈ [0,2] ∧ a 40 ∈ [0,1] ∧ a 26 ∈ [0,2] ∧ a 41 ∈ [0,2] ∧ a 28 ∈ [0] ∧ a 19 ∈ [0,1] ∧ a 23 ∈ [0] ∧ a 45 ∈ [0,1] ∧ a 20 ∈ [0] ∧ a 49 ∈ [0,2] := by
  have b0 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r42 v u) (a 25) (a 10) 3 d10 c42 (by decide +kernel)
  have t0 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] d25 b0
  have b1 : a 40 ≠ 2 := exclude [0,1] (fun u v => edge r43 v u) (a 40) (a 10) 2 d10 c43 (by decide +kernel)
  have t1 : a 40 ∈ [0,1,3] := remove (a 40) 2 [0,1,2,3] d40 b1
  have b2 : a 40 ≠ 3 := exclude [0,1] (fun u v => edge r43 v u) (a 40) (a 10) 3 d10 c43 (by decide +kernel)
  have t2 : a 40 ∈ [0,1] := remove (a 40) 3 [0,1,3] t1 b2
  have b3 : a 26 ≠ 1 := exclude [0,1] (fun u v => edge r46 v u) (a 26) (a 11) 1 d11 c46 (by decide +kernel)
  have t3 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b3
  have b4 : a 26 ≠ 3 := exclude [0,1] (fun u v => edge r46 v u) (a 26) (a 11) 3 d11 c46 (by decide +kernel)
  have t4 : a 26 ∈ [0,2] := remove (a 26) 3 [0,2,3] t3 b4
  have b5 : a 41 ≠ 1 := exclude [0,1] (fun u v => edge r47 v u) (a 41) (a 11) 1 d11 c47 (by decide +kernel)
  have t5 : a 41 ∈ [0,2,3] := remove (a 41) 1 [0,1,2,3] d41 b5
  have b6 : a 41 ≠ 3 := exclude [0,1] (fun u v => edge r47 v u) (a 41) (a 11) 3 d11 c47 (by decide +kernel)
  have t6 : a 41 ∈ [0,2] := remove (a 41) 3 [0,2,3] t5 b6
  have b7 : a 28 ≠ 1 := exclude [0,1] (fun u v => edge r52 v u) (a 28) (a 13) 1 d13 c52 (by decide +kernel)
  have t7 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b7
  have b8 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r60 v u) (a 19) (a 16) 2 d16 c60 (by decide +kernel)
  have t8 : a 19 ∈ [0,1,3] := remove (a 19) 2 [0,1,2,3] d19 b8
  have b9 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r60 v u) (a 19) (a 16) 3 d16 c60 (by decide +kernel)
  have t9 : a 19 ∈ [0,1] := remove (a 19) 3 [0,1,3] t8 b9
  have b10 : a 23 ≠ 1 := exclude [0,1] (fun u v => edge r61 v u) (a 23) (a 16) 1 d16 c61 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b10
  have b11 : a 45 ≠ 2 := exclude [0,1] (fun u v => edge r62 v u) (a 45) (a 16) 2 d16 c62 (by decide +kernel)
  have t11 : a 45 ∈ [0,1,3] := remove (a 45) 2 [0,1,2,3] d45 b11
  have b12 : a 45 ≠ 3 := exclude [0,1] (fun u v => edge r62 v u) (a 45) (a 16) 3 d16 c62 (by decide +kernel)
  have t12 : a 45 ∈ [0,1] := remove (a 45) 3 [0,1,3] t11 b12
  have b13 : a 20 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 20) (a 18) 1 d18 c67 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b13
  have b14 : a 49 ≠ 1 := exclude [0,1] (fun u v => edge r72 v u) (a 49) (a 19) 1 t9 c72 (by decide +kernel)
  have t14 : a 49 ∈ [0,2,3] := remove (a 49) 1 [0,1,2,3] d49 b14
  have b15 : a 49 ≠ 3 := exclude [0,1] (fun u v => edge r72 v u) (a 49) (a 19) 3 t9 c72 (by decide +kernel)
  have t15 : a 49 ∈ [0,2] := remove (a 49) 3 [0,2,3] t14 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (t15)))))))))

theorem chunk2 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0,2])
    (d51 : a 51 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0])
    (d52 : a 52 ∈ [0,1])
    (d54 : a 54 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,2])
    (d56 : a 56 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0])
    (d34 : a 34 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1])
    (d38 : a 38 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,2])
    (d39 : a 39 ∈ [0,1])
    (c78 : edge r78 (a 22) (a 24)=true)
    (c82 : edge r82 (a 23) (a 51)=true)
    (c85 : edge r85 (a 24) (a 52)=true)
    (c90 : edge r90 (a 26) (a 54)=true)
    (c94 : edge r94 (a 28) (a 56)=true)
    (c101 : edge r101 (a 31) (a 34)=true)
    (c102 : edge r102 (a 31) (a 38)=true)
    (c104 : edge r104 (a 32) (a 35)=true)
    (c105 : edge r105 (a 32) (a 39)=true)
    : a 24 ∈ [0,2] ∧ a 51 ∈ [0,2] ∧ a 52 ∈ [0] ∧ a 54 ∈ [0,2] ∧ a 56 ∈ [0,1] ∧ a 34 ∈ [0,2] ∧ a 38 ∈ [0,1] ∧ a 35 ∈ [0,1] ∧ a 39 ∈ [0] := by
  have b0 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r78 v u) (a 24) (a 22) 1 d22 c78 (by decide +kernel)
  have t0 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b0
  have b1 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r78 v u) (a 24) (a 22) 3 d22 c78 (by decide +kernel)
  have t1 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t0 b1
  have b2 : a 51 ≠ 1 := exclude [0] (fun u v => edge r82 v u) (a 51) (a 23) 1 d23 c82 (by decide +kernel)
  have t2 : a 51 ∈ [0,2,3] := remove (a 51) 1 [0,1,2,3] d51 b2
  have b3 : a 51 ≠ 3 := exclude [0] (fun u v => edge r82 v u) (a 51) (a 23) 3 d23 c82 (by decide +kernel)
  have t3 : a 51 ∈ [0,2] := remove (a 51) 3 [0,2,3] t2 b3
  have b4 : a 52 ≠ 1 := exclude [0,2] (fun u v => edge r85 v u) (a 52) (a 24) 1 t1 c85 (by decide +kernel)
  have t4 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b4
  have b5 : a 54 ≠ 1 := exclude [0,2] (fun u v => edge r90 v u) (a 54) (a 26) 1 d26 c90 (by decide +kernel)
  have t5 : a 54 ∈ [0,2,3] := remove (a 54) 1 [0,1,2,3] d54 b5
  have b6 : a 54 ≠ 3 := exclude [0,2] (fun u v => edge r90 v u) (a 54) (a 26) 3 d26 c90 (by decide +kernel)
  have t6 : a 54 ∈ [0,2] := remove (a 54) 3 [0,2,3] t5 b6
  have b7 : a 56 ≠ 2 := exclude [0] (fun u v => edge r94 v u) (a 56) (a 28) 2 d28 c94 (by decide +kernel)
  have t7 : a 56 ∈ [0,1,3] := remove (a 56) 2 [0,1,2,3] d56 b7
  have b8 : a 56 ≠ 3 := exclude [0] (fun u v => edge r94 v u) (a 56) (a 28) 3 d28 c94 (by decide +kernel)
  have t8 : a 56 ∈ [0,1] := remove (a 56) 3 [0,1,3] t7 b8
  have b9 : a 34 ≠ 1 := exclude [0,1] (fun u v => edge r101 v u) (a 34) (a 31) 1 d31 c101 (by decide +kernel)
  have t9 : a 34 ∈ [0,2,3] := remove (a 34) 1 [0,1,2,3] d34 b9
  have b10 : a 34 ≠ 3 := exclude [0,1] (fun u v => edge r101 v u) (a 34) (a 31) 3 d31 c101 (by decide +kernel)
  have t10 : a 34 ∈ [0,2] := remove (a 34) 3 [0,2,3] t9 b10
  have b11 : a 38 ≠ 2 := exclude [0,1] (fun u v => edge r102 v u) (a 38) (a 31) 2 d31 c102 (by decide +kernel)
  have t11 : a 38 ∈ [0,1,3] := remove (a 38) 2 [0,1,2,3] d38 b11
  have b12 : a 38 ≠ 3 := exclude [0,1] (fun u v => edge r102 v u) (a 38) (a 31) 3 d31 c102 (by decide +kernel)
  have t12 : a 38 ∈ [0,1] := remove (a 38) 3 [0,1,3] t11 b12
  have b13 : a 35 ≠ 2 := exclude [0,2] (fun u v => edge r104 v u) (a 35) (a 32) 2 d32 c104 (by decide +kernel)
  have t13 : a 35 ∈ [0,1,3] := remove (a 35) 2 [0,1,2,3] d35 b13
  have b14 : a 35 ≠ 3 := exclude [0,2] (fun u v => edge r104 v u) (a 35) (a 32) 3 d32 c104 (by decide +kernel)
  have t14 : a 35 ∈ [0,1] := remove (a 35) 3 [0,1,3] t13 b14
  have b15 : a 39 ≠ 1 := exclude [0,2] (fun u v => edge r105 v u) (a 39) (a 32) 1 d32 c105 (by decide +kernel)
  have t15 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b15
  exact And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk3 (a : Nat → Nat)
    (d46 : a 46 ∈ [0,1])
    (d32 : a 32 ∈ [0,2])
    (d44 : a 44 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d47 : a 47 ∈ [0,1,2,3])
    (d55 : a 55 ∈ [0,1])
    (d49 : a 49 ∈ [0,2])
    (d57 : a 57 ∈ [0,1,2,3])
    (c106 : edge r106 (a 32) (a 46)=true)
    (c132 : edge r132 (a 44) (a 45)=true)
    (c135 : edge r135 (a 45) (a 47)=true)
    (c145 : edge r145 (a 49) (a 55)=true)
    (c154 : edge r154 (a 55) (a 57)=true)
    : a 46 ∈ [0] ∧ a 44 ∈ [0] ∧ a 47 ∈ [0,1] ∧ a 55 ∈ [0] ∧ a 57 ∈ [0,2] := by
  have b0 : a 46 ≠ 1 := exclude [0,2] (fun u v => edge r106 v u) (a 46) (a 32) 1 d32 c106 (by decide +kernel)
  have t0 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b0
  have b1 : a 44 ≠ 1 := exclude [0,1] (edge r132) (a 44) (a 45) 1 d45 c132 (by decide +kernel)
  have t1 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b1
  have b2 : a 47 ≠ 2 := exclude [0,1] (fun u v => edge r135 v u) (a 47) (a 45) 2 d45 c135 (by decide +kernel)
  have t2 : a 47 ∈ [0,1,3] := remove (a 47) 2 [0,1,2,3] d47 b2
  have b3 : a 47 ≠ 3 := exclude [0,1] (fun u v => edge r135 v u) (a 47) (a 45) 3 d45 c135 (by decide +kernel)
  have t3 : a 47 ∈ [0,1] := remove (a 47) 3 [0,1,3] t2 b3
  have b4 : a 55 ≠ 1 := exclude [0,2] (fun u v => edge r145 v u) (a 55) (a 49) 1 d49 c145 (by decide +kernel)
  have t4 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b4
  have b5 : a 57 ≠ 1 := exclude [0] (fun u v => edge r154 v u) (a 57) (a 55) 1 t4 c154 (by decide +kernel)
  have t5 : a 57 ∈ [0,2,3] := remove (a 57) 1 [0,1,2,3] d57 b5
  have b6 : a 57 ≠ 3 := exclude [0] (fun u v => edge r154 v u) (a 57) (a 55) 3 t4 c154 (by decide +kernel)
  have t6 : a 57 ∈ [0,2] := remove (a 57) 3 [0,2,3] t5 b6
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t4 (t6))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_223
