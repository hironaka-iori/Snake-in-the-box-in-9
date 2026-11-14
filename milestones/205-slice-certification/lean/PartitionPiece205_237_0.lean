import PartitionData205_237
namespace PartitionCover205_237
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1])
    (d3 : a 3 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d32 : a 32 ∈ [0,1])
    (d5 : a 5 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (c5 : edge r5 (a 0) (a 29)=true)
    (c7 : edge r7 (a 1) (a 8)=true)
    (c8 : edge r8 (a 1) (a 15)=true)
    (c15 : edge r15 (a 3) (a 6)=true)
    (c16 : edge r16 (a 3) (a 17)=true)
    (c17 : edge r17 (a 3) (a 32)=true)
    (c21 : edge r21 (a 5) (a 6)=true)
    (c22 : edge r22 (a 5) (a 12)=true)
    (c25 : edge r25 (a 6) (a 20)=true)
    (c26 : edge r26 (a 6) (a 35)=true)
    (c32 : edge r32 (a 8) (a 11)=true)
    (c33 : edge r33 (a 8) (a 22)=true)
    : a 29 ∈ [0,2] ∧ a 8 ∈ [0,2] ∧ a 15 ∈ [0,2] ∧ a 6 ∈ [0] ∧ a 17 ∈ [0] ∧ a 32 ∈ [0] ∧ a 5 ∈ [0,2] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 35 ∈ [0] ∧ a 11 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 29 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 29) (a 0) 1 d0 c5 (by decide +kernel)
  have t0 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b0
  have b1 : a 29 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 29) (a 0) 3 d0 c5 (by decide +kernel)
  have t1 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0,1] (fun u v => edge r7 v u) (a 8) (a 1) 1 d1 c7 (by decide +kernel)
  have t2 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b2
  have b3 : a 8 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 8) (a 1) 3 d1 c7 (by decide +kernel)
  have t3 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t2 b3
  have b4 : a 15 ≠ 1 := exclude [0,1] (fun u v => edge r8 v u) (a 15) (a 1) 1 d1 c8 (by decide +kernel)
  have t4 : a 15 ∈ [0,2,3] := remove (a 15) 1 [0,1,2,3] d15 b4
  have b5 : a 15 ≠ 3 := exclude [0,1] (fun u v => edge r8 v u) (a 15) (a 1) 3 d1 c8 (by decide +kernel)
  have t5 : a 15 ∈ [0,2] := remove (a 15) 3 [0,2,3] t4 b5
  have b6 : a 6 ≠ 1 := exclude [0,1] (fun u v => edge r15 v u) (a 6) (a 3) 1 d3 c15 (by decide +kernel)
  have t6 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b6
  have b7 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r16 v u) (a 17) (a 3) 1 d3 c16 (by decide +kernel)
  have t7 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b7
  have b8 : a 32 ≠ 1 := exclude [0,1] (fun u v => edge r17 v u) (a 32) (a 3) 1 d3 c17 (by decide +kernel)
  have t8 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b8
  have b9 : a 5 ≠ 1 := exclude [0] (edge r21) (a 5) (a 6) 1 t6 c21 (by decide +kernel)
  have t9 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b9
  have b10 : a 5 ≠ 3 := exclude [0] (edge r21) (a 5) (a 6) 3 t6 c21 (by decide +kernel)
  have t10 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t9 b10
  have b11 : a 12 ≠ 1 := exclude [0,2] (fun u v => edge r22 v u) (a 12) (a 5) 1 t10 c22 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b11
  have b12 : a 20 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 20) (a 6) 1 t6 c25 (by decide +kernel)
  have t12 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b12
  have b13 : a 35 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 35) (a 6) 1 t6 c26 (by decide +kernel)
  have t13 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b13
  have b14 : a 11 ≠ 1 := exclude [0,2] (fun u v => edge r32 v u) (a 11) (a 8) 1 t3 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b14
  have b15 : a 22 ≠ 1 := exclude [0,2] (fun u v => edge r33 v u) (a 22) (a 8) 1 t3 c33 (by decide +kernel)
  have t15 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))

theorem chunk1 (a : Nat → Nat)
    (d37 : a 37 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d41 : a 41 ∈ [0,1])
    (d27 : a 27 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
    (d45 : a 45 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0])
    (d24 : a 24 ∈ [0,1,2,3])
    (d47 : a 47 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,1,2,3])
    (c34 : edge r34 (a 8) (a 37)=true)
    (c35 : edge r35 (a 9) (a 12)=true)
    (c43 : edge r43 (a 11) (a 26)=true)
    (c44 : edge r44 (a 11) (a 41)=true)
    (c46 : edge r46 (a 12) (a 27)=true)
    (c56 : edge r56 (a 15) (a 19)=true)
    (c58 : edge r58 (a 15) (a 45)=true)
    (c59 : edge r59 (a 16) (a 17)=true)
    (c63 : edge r63 (a 17) (a 24)=true)
    (c64 : edge r64 (a 17) (a 47)=true)
    (c65 : edge r65 (a 18) (a 19)=true)
    : a 37 ∈ [0] ∧ a 9 ∈ [0,1] ∧ a 26 ∈ [0] ∧ a 41 ∈ [0] ∧ a 27 ∈ [0,1] ∧ a 19 ∈ [0] ∧ a 45 ∈ [0] ∧ a 16 ∈ [0,1] ∧ a 24 ∈ [0,2] ∧ a 47 ∈ [0,1] ∧ a 18 ∈ [0,2,3] := by
  have b0 : a 37 ≠ 1 := exclude [0,2] (fun u v => edge r34 v u) (a 37) (a 8) 1 d8 c34 (by decide +kernel)
  have t0 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b0
  have b1 : a 9 ≠ 2 := exclude [0] (edge r35) (a 9) (a 12) 2 d12 c35 (by decide +kernel)
  have t1 : a 9 ∈ [0,1,3] := remove (a 9) 2 [0,1,2,3] d9 b1
  have b2 : a 9 ≠ 3 := exclude [0] (edge r35) (a 9) (a 12) 3 d12 c35 (by decide +kernel)
  have t2 : a 9 ∈ [0,1] := remove (a 9) 3 [0,1,3] t1 b2
  have b3 : a 26 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 26) (a 11) 1 d11 c43 (by decide +kernel)
  have t3 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b3
  have b4 : a 41 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 41) (a 11) 1 d11 c44 (by decide +kernel)
  have t4 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b4
  have b5 : a 27 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 27) (a 12) 2 d12 c46 (by decide +kernel)
  have t5 : a 27 ∈ [0,1,3] := remove (a 27) 2 [0,1,2,3] d27 b5
  have b6 : a 27 ≠ 3 := exclude [0] (fun u v => edge r46 v u) (a 27) (a 12) 3 d12 c46 (by decide +kernel)
  have t6 : a 27 ∈ [0,1] := remove (a 27) 3 [0,1,3] t5 b6
  have b7 : a 19 ≠ 1 := exclude [0,2] (fun u v => edge r56 v u) (a 19) (a 15) 1 d15 c56 (by decide +kernel)
  have t7 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b7
  have b8 : a 45 ≠ 1 := exclude [0,2] (fun u v => edge r58 v u) (a 45) (a 15) 1 d15 c58 (by decide +kernel)
  have t8 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b8
  have b9 : a 16 ≠ 2 := exclude [0] (edge r59) (a 16) (a 17) 2 d17 c59 (by decide +kernel)
  have t9 : a 16 ∈ [0,1,3] := remove (a 16) 2 [0,1,2,3] d16 b9
  have b10 : a 16 ≠ 3 := exclude [0] (edge r59) (a 16) (a 17) 3 d17 c59 (by decide +kernel)
  have t10 : a 16 ∈ [0,1] := remove (a 16) 3 [0,1,3] t9 b10
  have b11 : a 24 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 24) (a 17) 1 d17 c63 (by decide +kernel)
  have t11 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b11
  have b12 : a 24 ≠ 3 := exclude [0] (fun u v => edge r63 v u) (a 24) (a 17) 3 d17 c63 (by decide +kernel)
  have t12 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t11 b12
  have b13 : a 47 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 47) (a 17) 2 d17 c64 (by decide +kernel)
  have t13 : a 47 ∈ [0,1,3] := remove (a 47) 2 [0,1,2,3] d47 b13
  have b14 : a 47 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 47) (a 17) 3 d17 c64 (by decide +kernel)
  have t14 : a 47 ∈ [0,1] := remove (a 47) 3 [0,1,3] t13 b14
  have b15 : a 18 ≠ 1 := exclude [0] (edge r65) (a 18) (a 19) 1 t7 c65 (by decide +kernel)
  have t15 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2,3])
    (d19 : a 19 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d48 : a 48 ∈ [0,1,2,3])
    (d50 : a 50 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3])
    (d22 : a 22 ∈ [0])
    (d51 : a 51 ∈ [0,1,2,3])
    (d53 : a 53 ∈ [0,1])
    (d24 : a 24 ∈ [0,2])
    (d54 : a 54 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,2])
    (d36 : a 36 ∈ [0,1,2,3])
    (c65 : edge r65 (a 18) (a 19)=true)
    (c66 : edge r66 (a 18) (a 25)=true)
    (c69 : edge r69 (a 19) (a 48)=true)
    (c71 : edge r71 (a 20) (a 50)=true)
    (c72 : edge r72 (a 21) (a 22)=true)
    (c77 : edge r77 (a 22) (a 51)=true)
    (c82 : edge r82 (a 24) (a 53)=true)
    (c85 : edge r85 (a 25) (a 54)=true)
    (c89 : edge r89 (a 27) (a 56)=true)
    (c92 : edge r92 (a 29) (a 31)=true)
    (c93 : edge r93 (a 29) (a 36)=true)
    : a 18 ∈ [0,2] ∧ a 25 ∈ [0] ∧ a 48 ∈ [0,1] ∧ a 50 ∈ [0] ∧ a 21 ∈ [0,1] ∧ a 51 ∈ [0,2] ∧ a 53 ∈ [0] ∧ a 54 ∈ [0] ∧ a 56 ∈ [0] ∧ a 31 ∈ [0,1] ∧ a 36 ∈ [0,2] := by
  have b0 : a 18 ≠ 3 := exclude [0] (edge r65) (a 18) (a 19) 3 d19 c65 (by decide +kernel)
  have t0 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] d18 b0
  have b1 : a 25 ≠ 1 := exclude [0,2] (fun u v => edge r66 v u) (a 25) (a 18) 1 t0 c66 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b1
  have b2 : a 48 ≠ 2 := exclude [0] (fun u v => edge r69 v u) (a 48) (a 19) 2 d19 c69 (by decide +kernel)
  have t2 : a 48 ∈ [0,1,3] := remove (a 48) 2 [0,1,2,3] d48 b2
  have b3 : a 48 ≠ 3 := exclude [0] (fun u v => edge r69 v u) (a 48) (a 19) 3 d19 c69 (by decide +kernel)
  have t3 : a 48 ∈ [0,1] := remove (a 48) 3 [0,1,3] t2 b3
  have b4 : a 50 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 50) (a 20) 1 d20 c71 (by decide +kernel)
  have t4 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b4
  have b5 : a 21 ≠ 2 := exclude [0] (edge r72) (a 21) (a 22) 2 d22 c72 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,3] := remove (a 21) 2 [0,1,2,3] d21 b5
  have b6 : a 21 ≠ 3 := exclude [0] (edge r72) (a 21) (a 22) 3 d22 c72 (by decide +kernel)
  have t6 : a 21 ∈ [0,1] := remove (a 21) 3 [0,1,3] t5 b6
  have b7 : a 51 ≠ 1 := exclude [0] (fun u v => edge r77 v u) (a 51) (a 22) 1 d22 c77 (by decide +kernel)
  have t7 : a 51 ∈ [0,2,3] := remove (a 51) 1 [0,1,2,3] d51 b7
  have b8 : a 51 ≠ 3 := exclude [0] (fun u v => edge r77 v u) (a 51) (a 22) 3 d22 c77 (by decide +kernel)
  have t8 : a 51 ∈ [0,2] := remove (a 51) 3 [0,2,3] t7 b8
  have b9 : a 53 ≠ 1 := exclude [0,2] (fun u v => edge r82 v u) (a 53) (a 24) 1 d24 c82 (by decide +kernel)
  have t9 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b9
  have b10 : a 54 ≠ 1 := exclude [0] (fun u v => edge r85 v u) (a 54) (a 25) 1 t1 c85 (by decide +kernel)
  have t10 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b10
  have b11 : a 56 ≠ 1 := exclude [0,1] (fun u v => edge r89 v u) (a 56) (a 27) 1 d27 c89 (by decide +kernel)
  have t11 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b11
  have b12 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r92 v u) (a 31) (a 29) 2 d29 c92 (by decide +kernel)
  have t12 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b12
  have b13 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r92 v u) (a 31) (a 29) 3 d29 c92 (by decide +kernel)
  have t13 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t12 b13
  have b14 : a 36 ≠ 1 := exclude [0,2] (fun u v => edge r93 v u) (a 36) (a 29) 1 d29 c93 (by decide +kernel)
  have t14 : a 36 ∈ [0,2,3] := remove (a 36) 1 [0,1,2,3] d36 b14
  have b15 : a 36 ≠ 3 := exclude [0,2] (fun u v => edge r93 v u) (a 36) (a 29) 3 d29 c93 (by decide +kernel)
  have t15 : a 36 ∈ [0,2] := remove (a 36) 3 [0,2,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (t15))))))))))

theorem chunk3 (a : Nat → Nat)
    (d44 : a 44 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,2])
    (d39 : a 39 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0])
    (d33 : a 33 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0])
    (d49 : a 49 ∈ [0,1,2,3])
    (d50 : a 50 ∈ [0])
    (d57 : a 57 ∈ [0,1,2,3])
    (d52 : a 52 ∈ [0,1,2,3])
    (d53 : a 53 ∈ [0])
    (c94 : edge r94 (a 29) (a 44)=true)
    (c104 : edge r104 (a 32) (a 39)=true)
    (c106 : edge r106 (a 33) (a 35)=true)
    (c145 : edge r145 (a 49) (a 50)=true)
    (c147 : edge r147 (a 50) (a 57)=true)
    (c150 : edge r150 (a 52) (a 53)=true)
    : a 44 ∈ [0,2] ∧ a 39 ∈ [0,2] ∧ a 33 ∈ [0,1] ∧ a 49 ∈ [0,2] ∧ a 57 ∈ [0,1] ∧ a 52 ∈ [0,1] := by
  have b0 : a 44 ≠ 1 := exclude [0,2] (fun u v => edge r94 v u) (a 44) (a 29) 1 d29 c94 (by decide +kernel)
  have t0 : a 44 ∈ [0,2,3] := remove (a 44) 1 [0,1,2,3] d44 b0
  have b1 : a 44 ≠ 3 := exclude [0,2] (fun u v => edge r94 v u) (a 44) (a 29) 3 d29 c94 (by decide +kernel)
  have t1 : a 44 ∈ [0,2] := remove (a 44) 3 [0,2,3] t0 b1
  have b2 : a 39 ≠ 1 := exclude [0] (fun u v => edge r104 v u) (a 39) (a 32) 1 d32 c104 (by decide +kernel)
  have t2 : a 39 ∈ [0,2,3] := remove (a 39) 1 [0,1,2,3] d39 b2
  have b3 : a 39 ≠ 3 := exclude [0] (fun u v => edge r104 v u) (a 39) (a 32) 3 d32 c104 (by decide +kernel)
  have t3 : a 39 ∈ [0,2] := remove (a 39) 3 [0,2,3] t2 b3
  have b4 : a 33 ≠ 2 := exclude [0] (edge r106) (a 33) (a 35) 2 d35 c106 (by decide +kernel)
  have t4 : a 33 ∈ [0,1,3] := remove (a 33) 2 [0,1,2,3] d33 b4
  have b5 : a 33 ≠ 3 := exclude [0] (edge r106) (a 33) (a 35) 3 d35 c106 (by decide +kernel)
  have t5 : a 33 ∈ [0,1] := remove (a 33) 3 [0,1,3] t4 b5
  have b6 : a 49 ≠ 1 := exclude [0] (edge r145) (a 49) (a 50) 1 d50 c145 (by decide +kernel)
  have t6 : a 49 ∈ [0,2,3] := remove (a 49) 1 [0,1,2,3] d49 b6
  have b7 : a 49 ≠ 3 := exclude [0] (edge r145) (a 49) (a 50) 3 d50 c145 (by decide +kernel)
  have t7 : a 49 ∈ [0,2] := remove (a 49) 3 [0,2,3] t6 b7
  have b8 : a 57 ≠ 2 := exclude [0] (fun u v => edge r147 v u) (a 57) (a 50) 2 d50 c147 (by decide +kernel)
  have t8 : a 57 ∈ [0,1,3] := remove (a 57) 2 [0,1,2,3] d57 b8
  have b9 : a 57 ≠ 3 := exclude [0] (fun u v => edge r147 v u) (a 57) (a 50) 3 d50 c147 (by decide +kernel)
  have t9 : a 57 ∈ [0,1] := remove (a 57) 3 [0,1,3] t8 b9
  have b10 : a 52 ≠ 2 := exclude [0] (edge r150) (a 52) (a 53) 2 d53 c150 (by decide +kernel)
  have t10 : a 52 ∈ [0,1,3] := remove (a 52) 2 [0,1,2,3] d52 b10
  have b11 : a 52 ≠ 3 := exclude [0] (edge r150) (a 52) (a 53) 3 d53 c150 (by decide +kernel)
  have t11 : a 52 ∈ [0,1] := remove (a 52) 3 [0,1,3] t10 b11
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (t11)))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_237
