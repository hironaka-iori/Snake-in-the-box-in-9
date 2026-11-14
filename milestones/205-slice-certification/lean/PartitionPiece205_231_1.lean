import PartitionData205_231
namespace PartitionCover205_231
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d33 : a 33 ∈ [0,2])
    (d7 : a 7 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d35 : a 35 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d22 : a 22 ∈ [0,1])
    (d37 : a 37 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d40 : a 40 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d42 : a 42 ∈ [0,2])
    (c11 : edge r11 (a 2) (a 3)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 18)=true)
    (c15 : edge r15 (a 2) (a 33)=true)
    (c16 : edge r16 (a 3) (a 7)=true)
    (c23 : edge r23 (a 5) (a 7)=true)
    (c26 : edge r26 (a 5) (a 35)=true)
    (c31 : edge r31 (a 7) (a 15)=true)
    (c32 : edge r32 (a 7) (a 22)=true)
    (c33 : edge r33 (a 7) (a 37)=true)
    (c35 : edge r35 (a 8) (a 10)=true)
    (c36 : edge r36 (a 8) (a 12)=true)
    (c44 : edge r44 (a 10) (a 14)=true)
    (c46 : edge r46 (a 10) (a 40)=true)
    (c52 : edge r52 (a 12) (a 27)=true)
    (c53 : edge r53 (a 12) (a 42)=true)
    : a 3 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 33 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 35 ∈ [0] ∧ a 15 ∈ [0] ∧ a 22 ∈ [0] ∧ a 37 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 14 ∈ [0] ∧ a 40 ∈ [0] ∧ a 27 ∈ [0] ∧ a 42 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 3) (a 2) 1 d2 c11 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 10 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 1 d2 c13 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b1
  have b2 : a 18 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 18) (a 2) 1 d2 c14 (by decide +kernel)
  have t2 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b2
  have b3 : a 33 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 33) (a 2) 2 d2 c15 (by decide +kernel)
  have t3 : a 33 ∈ [0] := remove (a 33) 2 [0,2] d33 b3
  have b4 : a 7 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 7) (a 3) 1 t0 c16 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b4
  have b5 : a 5 ≠ 1 := exclude [0] (edge r23) (a 5) (a 7) 1 t4 c23 (by decide +kernel)
  have t5 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b5
  have b6 : a 35 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 35) (a 5) 2 t5 c26 (by decide +kernel)
  have t6 : a 35 ∈ [0] := remove (a 35) 2 [0,2] d35 b6
  have b7 : a 15 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 15) (a 7) 2 t4 c31 (by decide +kernel)
  have t7 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b7
  have b8 : a 22 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 22) (a 7) 1 t4 c32 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b8
  have b9 : a 37 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 37) (a 7) 1 t4 c33 (by decide +kernel)
  have t9 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b9
  have b10 : a 8 ≠ 2 := exclude [0] (edge r35) (a 8) (a 10) 2 t1 c35 (by decide +kernel)
  have t10 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b10
  have b11 : a 12 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 12) (a 8) 2 t10 c36 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b11
  have b12 : a 14 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 14) (a 10) 2 t1 c44 (by decide +kernel)
  have t12 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b12
  have b13 : a 40 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 40) (a 10) 2 t1 c46 (by decide +kernel)
  have t13 : a 40 ∈ [0] := remove (a 40) 2 [0,2] d40 b13
  have b14 : a 27 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 27) (a 12) 1 t11 c52 (by decide +kernel)
  have t14 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b14
  have b15 : a 42 ≠ 2 := exclude [0] (fun u v => edge r53 v u) (a 42) (a 12) 2 t11 c53 (by decide +kernel)
  have t15 : a 42 ∈ [0] := remove (a 42) 2 [0,2] d42 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d44 : a 44 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d19 : a 19 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d26 : a 26 ∈ [0,2])
    (d56 : a 56 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d57 : a 57 ∈ [0,2])
    (d58 : a 58 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d33 : a 33 ∈ [0])
    (d32 : a 32 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (d39 : a 39 ∈ [0,2])
    (c58 : edge r58 (a 14) (a 29)=true)
    (c59 : edge r59 (a 15) (a 30)=true)
    (c60 : edge r60 (a 15) (a 44)=true)
    (c62 : edge r62 (a 16) (a 18)=true)
    (c63 : edge r63 (a 16) (a 19)=true)
    (c69 : edge r69 (a 18) (a 21)=true)
    (c75 : edge r75 (a 19) (a 49)=true)
    (c83 : edge r83 (a 22) (a 52)=true)
    (c94 : edge r94 (a 26) (a 30)=true)
    (c95 : edge r95 (a 26) (a 56)=true)
    (c96 : edge r96 (a 27) (a 28)=true)
    (c99 : edge r99 (a 28) (a 57)=true)
    (c101 : edge r101 (a 29) (a 58)=true)
    (c104 : edge r104 (a 31) (a 33)=true)
    (c108 : edge r108 (a 32) (a 35)=true)
    (c109 : edge r109 (a 32) (a 39)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 44 ∈ [0] ∧ a 16 ∈ [0] ∧ a 19 ∈ [0] ∧ a 21 ∈ [0] ∧ a 49 ∈ [0] ∧ a 52 ∈ [0] ∧ a 26 ∈ [0] ∧ a 56 ∈ [0] ∧ a 28 ∈ [0] ∧ a 57 ∈ [0] ∧ a 58 ∈ [0] ∧ a 31 ∈ [0] ∧ a 32 ∈ [0] ∧ a 39 ∈ [0] := by
  have b0 : a 29 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 29) (a 14) 1 d14 c58 (by decide +kernel)
  have t0 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b0
  have b1 : a 30 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 30) (a 15) 1 d15 c59 (by decide +kernel)
  have t1 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b1
  have b2 : a 44 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 44) (a 15) 1 d15 c60 (by decide +kernel)
  have t2 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b2
  have b3 : a 16 ≠ 1 := exclude [0] (edge r62) (a 16) (a 18) 1 d18 c62 (by decide +kernel)
  have t3 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b3
  have b4 : a 19 ≠ 2 := exclude [0] (fun u v => edge r63 v u) (a 19) (a 16) 2 t3 c63 (by decide +kernel)
  have t4 : a 19 ∈ [0] := remove (a 19) 2 [0,2] d19 b4
  have b5 : a 21 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 21) (a 18) 1 d18 c69 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b5
  have b6 : a 49 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 49) (a 19) 1 t4 c75 (by decide +kernel)
  have t6 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b6
  have b7 : a 52 ≠ 1 := exclude [0] (fun u v => edge r83 v u) (a 52) (a 22) 1 d22 c83 (by decide +kernel)
  have t7 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b7
  have b8 : a 26 ≠ 2 := exclude [0] (edge r94) (a 26) (a 30) 2 t1 c94 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b8
  have b9 : a 56 ≠ 2 := exclude [0] (fun u v => edge r95 v u) (a 56) (a 26) 2 t8 c95 (by decide +kernel)
  have t9 : a 56 ∈ [0] := remove (a 56) 2 [0,2] d56 b9
  have b10 : a 28 ≠ 1 := exclude [0] (fun u v => edge r96 v u) (a 28) (a 27) 1 d27 c96 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b10
  have b11 : a 57 ≠ 2 := exclude [0] (fun u v => edge r99 v u) (a 57) (a 28) 2 t10 c99 (by decide +kernel)
  have t11 : a 57 ∈ [0] := remove (a 57) 2 [0,2] d57 b11
  have b12 : a 58 ≠ 1 := exclude [0] (fun u v => edge r101 v u) (a 58) (a 29) 1 t0 c101 (by decide +kernel)
  have t12 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b12
  have b13 : a 31 ≠ 1 := exclude [0] (edge r104) (a 31) (a 33) 1 d33 c104 (by decide +kernel)
  have t13 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b13
  have b14 : a 32 ≠ 1 := exclude [0] (edge r108) (a 32) (a 35) 1 d35 c108 (by decide +kernel)
  have t14 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b14
  have b15 : a 39 ≠ 2 := exclude [0] (fun u v => edge r109 v u) (a 39) (a 32) 2 t14 c109 (by decide +kernel)
  have t15 : a 39 ∈ [0] := remove (a 39) 2 [0,2] d39 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d46 : a 46 ∈ [0,1])
    (d32 : a 32 ∈ [0])
    (d43 : a 43 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d39 : a 39 ∈ [0])
    (d54 : a 54 ∈ [0,2])
    (d55 : a 55 ∈ [0,1])
    (d40 : a 40 ∈ [0])
    (d48 : a 48 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d5 : a 5 ∈ [0])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (c18 : edge r18 (a 4) (a 5)=true)
    (c34 : edge r34 (a 8) (a 9)=true)
    (c41 : edge r41 (a 9) (a 24)=true)
    (c61 : edge r61 (a 16) (a 17)=true)
    (c110 : edge r110 (a 32) (a 46)=true)
    (c119 : edge r119 (a 35) (a 43)=true)
    (c120 : edge r120 (a 35) (a 50)=true)
    (c129 : edge r129 (a 39) (a 41)=true)
    (c131 : edge r131 (a 39) (a 54)=true)
    (c133 : edge r133 (a 40) (a 55)=true)
    (c144 : edge r144 (a 46) (a 48)=true)
    (c159 : edge r159 (a 53) (a 54)=true)
    : a 46 ∈ [0] ∧ a 43 ∈ [0] ∧ a 50 ∈ [0] ∧ a 41 ∈ [0] ∧ a 54 ∈ [0] ∧ a 55 ∈ [0] ∧ a 48 ∈ [0] ∧ a 53 ∈ [0] ∧ a 4 ∈ [0] ∧ a 9 ∈ [0] ∧ a 24 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 46 ≠ 1 := exclude [0] (fun u v => edge r110 v u) (a 46) (a 32) 1 d32 c110 (by decide +kernel)
  have t0 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b0
  have b1 : a 43 ≠ 1 := exclude [0] (fun u v => edge r119 v u) (a 43) (a 35) 1 d35 c119 (by decide +kernel)
  have t1 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b1
  have b2 : a 50 ≠ 1 := exclude [0] (fun u v => edge r120 v u) (a 50) (a 35) 1 d35 c120 (by decide +kernel)
  have t2 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b2
  have b3 : a 41 ≠ 1 := exclude [0] (fun u v => edge r129 v u) (a 41) (a 39) 1 d39 c129 (by decide +kernel)
  have t3 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b3
  have b4 : a 54 ≠ 2 := exclude [0] (fun u v => edge r131 v u) (a 54) (a 39) 2 d39 c131 (by decide +kernel)
  have t4 : a 54 ∈ [0] := remove (a 54) 2 [0,2] d54 b4
  have b5 : a 55 ≠ 1 := exclude [0] (fun u v => edge r133 v u) (a 55) (a 40) 1 d40 c133 (by decide +kernel)
  have t5 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b5
  have b6 : a 48 ≠ 1 := exclude [0] (fun u v => edge r144 v u) (a 48) (a 46) 1 t0 c144 (by decide +kernel)
  have t6 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b6
  have b7 : a 53 ≠ 1 := exclude [0] (edge r159) (a 53) (a 54) 1 t4 c159 (by decide +kernel)
  have t7 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b7
  have b8 : a 4 ≠ 2 := exclude [0] (edge r18) (a 4) (a 5) 2 d5 c18 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b8
  have b9 : a 9 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 9) (a 8) 1 d8 c34 (by decide +kernel)
  have t9 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b9
  have b10 : a 24 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 24) (a 9) 1 t9 c41 (by decide +kernel)
  have t10 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b10
  have b11 : a 17 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 17) (a 16) 1 d16 c61 (by decide +kernel)
  have t11 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b11
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t11)))))))))))

theorem chunk7 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d33 : a 33 ∈ [0,2])
    (d7 : a 7 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d35 : a 35 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d22 : a 22 ∈ [0,1])
    (d37 : a 37 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d40 : a 40 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d42 : a 42 ∈ [0,2])
    (c11 : edge r11 (a 2) (a 3)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 18)=true)
    (c15 : edge r15 (a 2) (a 33)=true)
    (c16 : edge r16 (a 3) (a 7)=true)
    (c23 : edge r23 (a 5) (a 7)=true)
    (c26 : edge r26 (a 5) (a 35)=true)
    (c31 : edge r31 (a 7) (a 15)=true)
    (c32 : edge r32 (a 7) (a 22)=true)
    (c33 : edge r33 (a 7) (a 37)=true)
    (c35 : edge r35 (a 8) (a 10)=true)
    (c36 : edge r36 (a 8) (a 12)=true)
    (c44 : edge r44 (a 10) (a 14)=true)
    (c46 : edge r46 (a 10) (a 40)=true)
    (c52 : edge r52 (a 12) (a 27)=true)
    (c53 : edge r53 (a 12) (a 42)=true)
    : a 3 ∈ [1] ∧ a 10 ∈ [1] ∧ a 18 ∈ [1] ∧ a 33 ∈ [2] ∧ a 7 ∈ [1] ∧ a 5 ∈ [1] ∧ a 35 ∈ [2] ∧ a 15 ∈ [2] ∧ a 22 ∈ [1] ∧ a 37 ∈ [1] ∧ a 8 ∈ [2] ∧ a 12 ∈ [2] ∧ a 14 ∈ [2] ∧ a 40 ∈ [2] ∧ a 27 ∈ [1] ∧ a 42 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 3) (a 2) 0 d2 c11 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 10 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 10) (a 2) 0 d2 c13 (by decide +kernel)
  have t1 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b1
  have b2 : a 18 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 18) (a 2) 0 d2 c14 (by decide +kernel)
  have t2 : a 18 ∈ [1] := remove (a 18) 0 [0,1] d18 b2
  have b3 : a 33 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 33) (a 2) 0 d2 c15 (by decide +kernel)
  have t3 : a 33 ∈ [2] := remove (a 33) 0 [0,2] d33 b3
  have b4 : a 7 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 7) (a 3) 0 t0 c16 (by decide +kernel)
  have t4 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b4
  have b5 : a 5 ≠ 0 := exclude [1] (edge r23) (a 5) (a 7) 0 t4 c23 (by decide +kernel)
  have t5 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b5
  have b6 : a 35 ≠ 0 := exclude [1] (fun u v => edge r26 v u) (a 35) (a 5) 0 t5 c26 (by decide +kernel)
  have t6 : a 35 ∈ [2] := remove (a 35) 0 [0,2] d35 b6
  have b7 : a 15 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 15) (a 7) 0 t4 c31 (by decide +kernel)
  have t7 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b7
  have b8 : a 22 ≠ 0 := exclude [1] (fun u v => edge r32 v u) (a 22) (a 7) 0 t4 c32 (by decide +kernel)
  have t8 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b8
  have b9 : a 37 ≠ 0 := exclude [1] (fun u v => edge r33 v u) (a 37) (a 7) 0 t4 c33 (by decide +kernel)
  have t9 : a 37 ∈ [1] := remove (a 37) 0 [0,1] d37 b9
  have b10 : a 8 ≠ 0 := exclude [1] (edge r35) (a 8) (a 10) 0 t1 c35 (by decide +kernel)
  have t10 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b10
  have b11 : a 12 ≠ 0 := exclude [2] (fun u v => edge r36 v u) (a 12) (a 8) 0 t10 c36 (by decide +kernel)
  have t11 : a 12 ∈ [2] := remove (a 12) 0 [0,2] d12 b11
  have b12 : a 14 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 14) (a 10) 0 t1 c44 (by decide +kernel)
  have t12 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b12
  have b13 : a 40 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 40) (a 10) 0 t1 c46 (by decide +kernel)
  have t13 : a 40 ∈ [2] := remove (a 40) 0 [0,2] d40 b13
  have b14 : a 27 ≠ 0 := exclude [2] (fun u v => edge r52 v u) (a 27) (a 12) 0 t11 c52 (by decide +kernel)
  have t14 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b14
  have b15 : a 42 ≠ 0 := exclude [2] (fun u v => edge r53 v u) (a 42) (a 12) 0 t11 c53 (by decide +kernel)
  have t15 : a 42 ∈ [2] := remove (a 42) 0 [0,2] d42 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_231
