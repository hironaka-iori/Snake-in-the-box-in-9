import PartitionData205_221
namespace PartitionCover205_221
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d36 : a 36 ∈ [0,2])
    (d38 : a 38 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d40 : a 40 ∈ [0,2])
    (d27 : a 27 ∈ [0,2])
    (d16 : a 16 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 18)=true)
    (c15 : edge r15 (a 2) (a 31)=true)
    (c20 : edge r20 (a 4) (a 6)=true)
    (c21 : edge r21 (a 4) (a 12)=true)
    (c22 : edge r22 (a 4) (a 19)=true)
    (c28 : edge r28 (a 6) (a 14)=true)
    (c34 : edge r34 (a 8) (a 10)=true)
    (c36 : edge r36 (a 8) (a 22)=true)
    (c37 : edge r37 (a 8) (a 36)=true)
    (c44 : edge r44 (a 10) (a 38)=true)
    (c50 : edge r50 (a 12) (a 25)=true)
    (c51 : edge r51 (a 12) (a 40)=true)
    (c56 : edge r56 (a 14) (a 27)=true)
    (c61 : edge r61 (a 16) (a 18)=true)
    : a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 31 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 19 ∈ [0] ∧ a 14 ∈ [0] ∧ a 8 ∈ [0] ∧ a 22 ∈ [0] ∧ a 36 ∈ [0] ∧ a 38 ∈ [0] ∧ a 25 ∈ [0] ∧ a 40 ∈ [0] ∧ a 27 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 6 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 6) (a 2) 1 d2 c12 (by decide +kernel)
  have t0 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b0
  have b1 : a 10 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 1 d2 c13 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b1
  have b2 : a 18 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 18) (a 2) 2 d2 c14 (by decide +kernel)
  have t2 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b2
  have b3 : a 31 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 31) (a 2) 1 d2 c15 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b3
  have b4 : a 4 ≠ 1 := exclude [0] (edge r20) (a 4) (a 6) 1 t0 c20 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b4
  have b5 : a 12 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 12) (a 4) 1 t4 c21 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b5
  have b6 : a 19 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 19) (a 4) 1 t4 c22 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b6
  have b7 : a 14 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 14) (a 6) 1 t0 c28 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b7
  have b8 : a 8 ≠ 1 := exclude [0] (edge r34) (a 8) (a 10) 1 t1 c34 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b8
  have b9 : a 22 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 22) (a 8) 1 t8 c36 (by decide +kernel)
  have t9 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b9
  have b10 : a 36 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 36) (a 8) 2 t8 c37 (by decide +kernel)
  have t10 : a 36 ∈ [0] := remove (a 36) 2 [0,2] d36 b10
  have b11 : a 38 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 38) (a 10) 1 t1 c44 (by decide +kernel)
  have t11 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b11
  have b12 : a 25 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 25) (a 12) 1 t5 c50 (by decide +kernel)
  have t12 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b12
  have b13 : a 40 ≠ 2 := exclude [0] (fun u v => edge r51 v u) (a 40) (a 12) 2 t5 c51 (by decide +kernel)
  have t13 : a 40 ∈ [0] := remove (a 40) 2 [0,2] d40 b13
  have b14 : a 27 ≠ 2 := exclude [0] (fun u v => edge r56 v u) (a 27) (a 14) 2 t7 c56 (by decide +kernel)
  have t14 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b14
  have b15 : a 16 ≠ 1 := exclude [0] (edge r61) (a 16) (a 18) 1 t2 c61 (by decide +kernel)
  have t15 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d48 : a 48 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d55 : a 55 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d57 : a 57 ∈ [0,2])
    (d27 : a 27 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d38 : a 38 ∈ [0])
    (d53 : a 53 ∈ [0,2])
    (d43 : a 43 ∈ [0,1])
    (d54 : a 54 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d40 : a 40 ∈ [0])
    (d47 : a 47 ∈ [0,1])
    (d49 : a 49 ∈ [0,2])
    (d50 : a 50 ∈ [0,1])
    (d51 : a 51 ∈ [0,2])
    (d52 : a 52 ∈ [0,2])
    (c71 : edge r71 (a 19) (a 48)=true)
    (c84 : edge r84 (a 25) (a 26)=true)
    (c86 : edge r86 (a 25) (a 55)=true)
    (c87 : edge r87 (a 26) (a 28)=true)
    (c90 : edge r90 (a 27) (a 57)=true)
    (c93 : edge r93 (a 29) (a 31)=true)
    (c121 : edge r121 (a 38) (a 39)=true)
    (c123 : edge r123 (a 38) (a 53)=true)
    (c124 : edge r124 (a 39) (a 43)=true)
    (c125 : edge r125 (a 39) (a 54)=true)
    (c126 : edge r126 (a 40) (a 41)=true)
    (c144 : edge r144 (a 47) (a 54)=true)
    (c145 : edge r145 (a 48) (a 49)=true)
    (c146 : edge r146 (a 48) (a 50)=true)
    (c148 : edge r148 (a 49) (a 51)=true)
    (c153 : edge r153 (a 52) (a 54)=true)
    : a 48 ∈ [0] ∧ a 26 ∈ [0] ∧ a 55 ∈ [0] ∧ a 28 ∈ [0] ∧ a 57 ∈ [0] ∧ a 29 ∈ [0] ∧ a 39 ∈ [0] ∧ a 53 ∈ [0] ∧ a 43 ∈ [0] ∧ a 54 ∈ [0] ∧ a 41 ∈ [0] ∧ a 47 ∈ [0] ∧ a 49 ∈ [0] ∧ a 50 ∈ [0] ∧ a 51 ∈ [0] ∧ a 52 ∈ [0] := by
  have b0 : a 48 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 48) (a 19) 1 d19 c71 (by decide +kernel)
  have t0 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b0
  have b1 : a 26 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 26) (a 25) 1 d25 c84 (by decide +kernel)
  have t1 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b1
  have b2 : a 55 ≠ 2 := exclude [0] (fun u v => edge r86 v u) (a 55) (a 25) 2 d25 c86 (by decide +kernel)
  have t2 : a 55 ∈ [0] := remove (a 55) 2 [0,2] d55 b2
  have b3 : a 28 ≠ 1 := exclude [0] (fun u v => edge r87 v u) (a 28) (a 26) 1 t1 c87 (by decide +kernel)
  have t3 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b3
  have b4 : a 57 ≠ 2 := exclude [0] (fun u v => edge r90 v u) (a 57) (a 27) 2 d27 c90 (by decide +kernel)
  have t4 : a 57 ∈ [0] := remove (a 57) 2 [0,2] d57 b4
  have b5 : a 29 ≠ 1 := exclude [0] (edge r93) (a 29) (a 31) 1 d31 c93 (by decide +kernel)
  have t5 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b5
  have b6 : a 39 ≠ 1 := exclude [0] (fun u v => edge r121 v u) (a 39) (a 38) 1 d38 c121 (by decide +kernel)
  have t6 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b6
  have b7 : a 53 ≠ 2 := exclude [0] (fun u v => edge r123 v u) (a 53) (a 38) 2 d38 c123 (by decide +kernel)
  have t7 : a 53 ∈ [0] := remove (a 53) 2 [0,2] d53 b7
  have b8 : a 43 ≠ 1 := exclude [0] (fun u v => edge r124 v u) (a 43) (a 39) 1 t6 c124 (by decide +kernel)
  have t8 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b8
  have b9 : a 54 ≠ 1 := exclude [0] (fun u v => edge r125 v u) (a 54) (a 39) 1 t6 c125 (by decide +kernel)
  have t9 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b9
  have b10 : a 41 ≠ 1 := exclude [0] (fun u v => edge r126 v u) (a 41) (a 40) 1 d40 c126 (by decide +kernel)
  have t10 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b10
  have b11 : a 47 ≠ 1 := exclude [0] (edge r144) (a 47) (a 54) 1 t9 c144 (by decide +kernel)
  have t11 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b11
  have b12 : a 49 ≠ 2 := exclude [0] (fun u v => edge r145 v u) (a 49) (a 48) 2 t0 c145 (by decide +kernel)
  have t12 : a 49 ∈ [0] := remove (a 49) 2 [0,2] d49 b12
  have b13 : a 50 ≠ 1 := exclude [0] (fun u v => edge r146 v u) (a 50) (a 48) 1 t0 c146 (by decide +kernel)
  have t13 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b13
  have b14 : a 51 ≠ 2 := exclude [0] (fun u v => edge r148 v u) (a 51) (a 49) 2 t12 c148 (by decide +kernel)
  have t14 : a 51 ∈ [0] := remove (a 51) 2 [0,2] d51 b14
  have b15 : a 52 ≠ 2 := exclude [0] (edge r153) (a 52) (a 54) 2 t9 c153 (by decide +kernel)
  have t15 : a 52 ∈ [0] := remove (a 52) 2 [0,2] d52 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d34 : a 34 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d8 : a 8 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (d45 : a 45 ∈ [0,1])
    (d21 : a 21 ∈ [0,2])
    (d28 : a 28 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d29 : a 29 ∈ [0])
    (c19 : edge r19 (a 4) (a 5)=true)
    (c26 : edge r26 (a 5) (a 34)=true)
    (c33 : edge r33 (a 8) (a 9)=true)
    (c60 : edge r60 (a 16) (a 17)=true)
    (c66 : edge r66 (a 17) (a 45)=true)
    (c75 : edge r75 (a 21) (a 28)=true)
    (c82 : edge r82 (a 24) (a 28)=true)
    (c92 : edge r92 (a 29) (a 30)=true)
    : a 5 ∈ [0] ∧ a 34 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 45 ∈ [0] ∧ a 21 ∈ [0] ∧ a 24 ∈ [0] ∧ a 30 ∈ [0] := by
  have b0 : a 5 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 5) (a 4) 1 d4 c19 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b0
  have b1 : a 34 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 34) (a 5) 1 t0 c26 (by decide +kernel)
  have t1 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b1
  have b2 : a 9 ≠ 2 := exclude [0] (fun u v => edge r33 v u) (a 9) (a 8) 2 d8 c33 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b2
  have b3 : a 17 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 17) (a 16) 1 d16 c60 (by decide +kernel)
  have t3 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b3
  have b4 : a 45 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 45) (a 17) 1 t3 c66 (by decide +kernel)
  have t4 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b4
  have b5 : a 21 ≠ 2 := exclude [0] (edge r75) (a 21) (a 28) 2 d28 c75 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b5
  have b6 : a 24 ≠ 1 := exclude [0] (edge r82) (a 24) (a 28) 1 d28 c82 (by decide +kernel)
  have t6 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b6
  have b7 : a 30 ≠ 2 := exclude [0] (fun u v => edge r92 v u) (a 30) (a 29) 2 d29 c92 (by decide +kernel)
  have t7 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk7 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d10 : a 10 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d36 : a 36 ∈ [0,2])
    (d38 : a 38 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d40 : a 40 ∈ [0,2])
    (d27 : a 27 ∈ [0,2])
    (d16 : a 16 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 18)=true)
    (c15 : edge r15 (a 2) (a 31)=true)
    (c20 : edge r20 (a 4) (a 6)=true)
    (c21 : edge r21 (a 4) (a 12)=true)
    (c22 : edge r22 (a 4) (a 19)=true)
    (c28 : edge r28 (a 6) (a 14)=true)
    (c34 : edge r34 (a 8) (a 10)=true)
    (c36 : edge r36 (a 8) (a 22)=true)
    (c37 : edge r37 (a 8) (a 36)=true)
    (c44 : edge r44 (a 10) (a 38)=true)
    (c50 : edge r50 (a 12) (a 25)=true)
    (c51 : edge r51 (a 12) (a 40)=true)
    (c56 : edge r56 (a 14) (a 27)=true)
    (c61 : edge r61 (a 16) (a 18)=true)
    : a 6 ∈ [1] ∧ a 10 ∈ [1] ∧ a 18 ∈ [2] ∧ a 31 ∈ [1] ∧ a 4 ∈ [1] ∧ a 12 ∈ [1] ∧ a 19 ∈ [1] ∧ a 14 ∈ [1] ∧ a 8 ∈ [1] ∧ a 22 ∈ [1] ∧ a 36 ∈ [2] ∧ a 38 ∈ [1] ∧ a 25 ∈ [1] ∧ a 40 ∈ [2] ∧ a 27 ∈ [2] ∧ a 16 ∈ [1] := by
  have b0 : a 6 ≠ 0 := exclude [1] (fun u v => edge r12 v u) (a 6) (a 2) 0 d2 c12 (by decide +kernel)
  have t0 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b0
  have b1 : a 10 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 10) (a 2) 0 d2 c13 (by decide +kernel)
  have t1 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b1
  have b2 : a 18 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 18) (a 2) 0 d2 c14 (by decide +kernel)
  have t2 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b2
  have b3 : a 31 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 31) (a 2) 0 d2 c15 (by decide +kernel)
  have t3 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b3
  have b4 : a 4 ≠ 0 := exclude [1] (edge r20) (a 4) (a 6) 0 t0 c20 (by decide +kernel)
  have t4 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b4
  have b5 : a 12 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 12) (a 4) 0 t4 c21 (by decide +kernel)
  have t5 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b5
  have b6 : a 19 ≠ 0 := exclude [1] (fun u v => edge r22 v u) (a 19) (a 4) 0 t4 c22 (by decide +kernel)
  have t6 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b6
  have b7 : a 14 ≠ 0 := exclude [1] (fun u v => edge r28 v u) (a 14) (a 6) 0 t0 c28 (by decide +kernel)
  have t7 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b7
  have b8 : a 8 ≠ 0 := exclude [1] (edge r34) (a 8) (a 10) 0 t1 c34 (by decide +kernel)
  have t8 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b8
  have b9 : a 22 ≠ 0 := exclude [1] (fun u v => edge r36 v u) (a 22) (a 8) 0 t8 c36 (by decide +kernel)
  have t9 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b9
  have b10 : a 36 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 36) (a 8) 0 t8 c37 (by decide +kernel)
  have t10 : a 36 ∈ [2] := remove (a 36) 0 [0,2] d36 b10
  have b11 : a 38 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 38) (a 10) 0 t1 c44 (by decide +kernel)
  have t11 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b11
  have b12 : a 25 ≠ 0 := exclude [1] (fun u v => edge r50 v u) (a 25) (a 12) 0 t5 c50 (by decide +kernel)
  have t12 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b12
  have b13 : a 40 ≠ 0 := exclude [1] (fun u v => edge r51 v u) (a 40) (a 12) 0 t5 c51 (by decide +kernel)
  have t13 : a 40 ∈ [2] := remove (a 40) 0 [0,2] d40 b13
  have b14 : a 27 ≠ 0 := exclude [1] (fun u v => edge r56 v u) (a 27) (a 14) 0 t7 c56 (by decide +kernel)
  have t14 : a 27 ∈ [2] := remove (a 27) 0 [0,2] d27 b14
  have b15 : a 16 ≠ 0 := exclude [2] (edge r61) (a 16) (a 18) 0 t2 c61 (by decide +kernel)
  have t15 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_221
