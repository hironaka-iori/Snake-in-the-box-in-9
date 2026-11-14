import PartitionData205_223
namespace PartitionCover205_223
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d32 : a 32 ∈ [0,2])
    (d4 : a 4 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d26 : a 26 ∈ [0,2])
    (d41 : a 41 ∈ [0,2])
    (d15 : a 15 ∈ [0,1])
    (d24 : a 24 ∈ [0,2])
    (d25 : a 25 ∈ [0,2])
    (d29 : a 29 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 17)=true)
    (c14 : edge r14 (a 2) (a 32)=true)
    (c18 : edge r18 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 11)=true)
    (c27 : edge r27 (a 6) (a 13)=true)
    (c29 : edge r29 (a 6) (a 35)=true)
    (c34 : edge r34 (a 8) (a 11)=true)
    (c35 : edge r35 (a 8) (a 22)=true)
    (c46 : edge r46 (a 11) (a 26)=true)
    (c47 : edge r47 (a 11) (a 41)=true)
    (c56 : edge r56 (a 15) (a 17)=true)
    (c64 : edge r64 (a 17) (a 24)=true)
    (c83 : edge r83 (a 24) (a 25)=true)
    (c86 : edge r86 (a 25) (a 29)=true)
    (c87 : edge r87 (a 25) (a 53)=true)
    : a 6 ∈ [0] ∧ a 17 ∈ [0] ∧ a 32 ∈ [0] ∧ a 4 ∈ [0] ∧ a 11 ∈ [0] ∧ a 13 ∈ [0] ∧ a 35 ∈ [0] ∧ a 8 ∈ [0] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0] ∧ a 41 ∈ [0] ∧ a 15 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 29 ∈ [0] ∧ a 53 ∈ [0] := by
  have b0 : a 6 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 6) (a 2) 1 d2 c12 (by decide +kernel)
  have t0 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b0
  have b1 : a 17 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 17) (a 2) 1 d2 c13 (by decide +kernel)
  have t1 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b1
  have b2 : a 32 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 32) (a 2) 2 d2 c14 (by decide +kernel)
  have t2 : a 32 ∈ [0] := remove (a 32) 2 [0,2] d32 b2
  have b3 : a 4 ≠ 2 := exclude [0] (edge r18) (a 4) (a 6) 2 t0 c18 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b3
  have b4 : a 11 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 11) (a 4) 1 t3 c19 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b4
  have b5 : a 13 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 13) (a 6) 1 t0 c27 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b5
  have b6 : a 35 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 35) (a 6) 1 t0 c29 (by decide +kernel)
  have t6 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b6
  have b7 : a 8 ≠ 1 := exclude [0] (edge r34) (a 8) (a 11) 1 t4 c34 (by decide +kernel)
  have t7 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b7
  have b8 : a 22 ≠ 2 := exclude [0] (fun u v => edge r35 v u) (a 22) (a 8) 2 t7 c35 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b8
  have b9 : a 26 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 26) (a 11) 2 t4 c46 (by decide +kernel)
  have t9 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b9
  have b10 : a 41 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 41) (a 11) 2 t4 c47 (by decide +kernel)
  have t10 : a 41 ∈ [0] := remove (a 41) 2 [0,2] d41 b10
  have b11 : a 15 ≠ 1 := exclude [0] (edge r56) (a 15) (a 17) 1 t1 c56 (by decide +kernel)
  have t11 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b11
  have b12 : a 24 ≠ 2 := exclude [0] (fun u v => edge r64 v u) (a 24) (a 17) 2 t1 c64 (by decide +kernel)
  have t12 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b12
  have b13 : a 25 ≠ 2 := exclude [0] (fun u v => edge r83 v u) (a 25) (a 24) 2 t12 c83 (by decide +kernel)
  have t13 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b13
  have b14 : a 29 ≠ 1 := exclude [0] (fun u v => edge r86 v u) (a 29) (a 25) 1 t13 c86 (by decide +kernel)
  have t14 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b14
  have b15 : a 53 ≠ 1 := exclude [0] (fun u v => edge r87 v u) (a 53) (a 25) 1 t13 c87 (by decide +kernel)
  have t15 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d54 : a 54 ∈ [0,2])
    (d57 : a 57 ∈ [0,2])
    (d29 : a 29 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d32 : a 32 ∈ [0])
    (d36 : a 36 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d41 : a 41 ∈ [0])
    (d47 : a 47 ∈ [0,1])
    (d53 : a 53 ∈ [0])
    (d48 : a 48 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d51 : a 51 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d19 : a 19 ∈ [0,1])
    (d34 : a 34 ∈ [0,2])
    (c17 : edge r17 (a 4) (a 5)=true)
    (c24 : edge r24 (a 5) (a 19)=true)
    (c25 : edge r25 (a 5) (a 34)=true)
    (c88 : edge r88 (a 26) (a 27)=true)
    (c90 : edge r90 (a 26) (a 54)=true)
    (c95 : edge r95 (a 29) (a 57)=true)
    (c97 : edge r97 (a 30) (a 32)=true)
    (c114 : edge r114 (a 35) (a 36)=true)
    (c115 : edge r115 (a 35) (a 50)=true)
    (c116 : edge r116 (a 36) (a 43)=true)
    (c125 : edge r125 (a 40) (a 43)=true)
    (c127 : edge r127 (a 41) (a 42)=true)
    (c141 : edge r141 (a 47) (a 53)=true)
    (c143 : edge r143 (a 48) (a 50)=true)
    (c146 : edge r146 (a 50) (a 56)=true)
    (c147 : edge r147 (a 51) (a 53)=true)
    : a 27 ∈ [0] ∧ a 54 ∈ [0] ∧ a 57 ∈ [0] ∧ a 30 ∈ [0] ∧ a 36 ∈ [0] ∧ a 50 ∈ [0] ∧ a 43 ∈ [0] ∧ a 40 ∈ [0] ∧ a 42 ∈ [0] ∧ a 47 ∈ [0] ∧ a 48 ∈ [0] ∧ a 56 ∈ [0] ∧ a 51 ∈ [0] ∧ a 5 ∈ [0] ∧ a 19 ∈ [0] ∧ a 34 ∈ [0] := by
  have b0 : a 27 ≠ 1 := exclude [0] (fun u v => edge r88 v u) (a 27) (a 26) 1 d26 c88 (by decide +kernel)
  have t0 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b0
  have b1 : a 54 ≠ 2 := exclude [0] (fun u v => edge r90 v u) (a 54) (a 26) 2 d26 c90 (by decide +kernel)
  have t1 : a 54 ∈ [0] := remove (a 54) 2 [0,2] d54 b1
  have b2 : a 57 ≠ 2 := exclude [0] (fun u v => edge r95 v u) (a 57) (a 29) 2 d29 c95 (by decide +kernel)
  have t2 : a 57 ∈ [0] := remove (a 57) 2 [0,2] d57 b2
  have b3 : a 30 ≠ 1 := exclude [0] (edge r97) (a 30) (a 32) 1 d32 c97 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b3
  have b4 : a 36 ≠ 1 := exclude [0] (fun u v => edge r114 v u) (a 36) (a 35) 1 d35 c114 (by decide +kernel)
  have t4 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b4
  have b5 : a 50 ≠ 1 := exclude [0] (fun u v => edge r115 v u) (a 50) (a 35) 1 d35 c115 (by decide +kernel)
  have t5 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b5
  have b6 : a 43 ≠ 1 := exclude [0] (fun u v => edge r116 v u) (a 43) (a 36) 1 t4 c116 (by decide +kernel)
  have t6 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b6
  have b7 : a 40 ≠ 1 := exclude [0] (edge r125) (a 40) (a 43) 1 t6 c125 (by decide +kernel)
  have t7 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b7
  have b8 : a 42 ≠ 1 := exclude [0] (fun u v => edge r127 v u) (a 42) (a 41) 1 d41 c127 (by decide +kernel)
  have t8 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b8
  have b9 : a 47 ≠ 1 := exclude [0] (edge r141) (a 47) (a 53) 1 d53 c141 (by decide +kernel)
  have t9 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b9
  have b10 : a 48 ≠ 1 := exclude [0] (edge r143) (a 48) (a 50) 1 t5 c143 (by decide +kernel)
  have t10 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b10
  have b11 : a 56 ≠ 1 := exclude [0] (fun u v => edge r146 v u) (a 56) (a 50) 1 t5 c146 (by decide +kernel)
  have t11 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b11
  have b12 : a 51 ≠ 2 := exclude [0] (edge r147) (a 51) (a 53) 2 d53 c147 (by decide +kernel)
  have t12 : a 51 ∈ [0] := remove (a 51) 2 [0,2] d51 b12
  have b13 : a 5 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 5) (a 4) 1 d4 c17 (by decide +kernel)
  have t13 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b13
  have b14 : a 19 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 19) (a 5) 1 t13 c24 (by decide +kernel)
  have t14 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b14
  have b15 : a 34 ≠ 2 := exclude [0] (fun u v => edge r25 v u) (a 34) (a 5) 2 t13 c25 (by decide +kernel)
  have t15 : a 34 ∈ [0] := remove (a 34) 2 [0,2] d34 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d45 : a 45 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d49 : a 49 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d30 : a 30 ∈ [0])
    (c33 : edge r33 (a 8) (a 9)=true)
    (c37 : edge r37 (a 9) (a 10)=true)
    (c40 : edge r40 (a 9) (a 38)=true)
    (c55 : edge r55 (a 15) (a 16)=true)
    (c62 : edge r62 (a 16) (a 45)=true)
    (c70 : edge r70 (a 19) (a 21)=true)
    (c72 : edge r72 (a 19) (a 49)=true)
    (c96 : edge r96 (a 30) (a 31)=true)
    : a 9 ∈ [0] ∧ a 10 ∈ [0] ∧ a 38 ∈ [0] ∧ a 16 ∈ [0] ∧ a 45 ∈ [0] ∧ a 21 ∈ [0] ∧ a 49 ∈ [0] ∧ a 31 ∈ [0] := by
  have b0 : a 9 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 9) (a 8) 1 d8 c33 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b0
  have b1 : a 10 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 10) (a 9) 1 t0 c37 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b1
  have b2 : a 38 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 38) (a 9) 1 t0 c40 (by decide +kernel)
  have t2 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b2
  have b3 : a 16 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 16) (a 15) 1 d15 c55 (by decide +kernel)
  have t3 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b3
  have b4 : a 45 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 45) (a 16) 1 t3 c62 (by decide +kernel)
  have t4 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b4
  have b5 : a 21 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 21) (a 19) 1 d19 c70 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b5
  have b6 : a 49 ≠ 2 := exclude [0] (fun u v => edge r72 v u) (a 49) (a 19) 2 d19 c72 (by decide +kernel)
  have t6 : a 49 ∈ [0] := remove (a 49) 2 [0,2] d49 b6
  have b7 : a 31 ≠ 1 := exclude [0] (fun u v => edge r96 v u) (a 31) (a 30) 1 d30 c96 (by decide +kernel)
  have t7 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk7 (a : Nat → Nat)
    (d6 : a 6 ∈ [0,1])
    (d2 : a 2 ∈ [2])
    (d17 : a 17 ∈ [0,1])
    (d32 : a 32 ∈ [0,2])
    (d4 : a 4 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d26 : a 26 ∈ [0,2])
    (d41 : a 41 ∈ [0,2])
    (d15 : a 15 ∈ [0,1])
    (d24 : a 24 ∈ [0,2])
    (d25 : a 25 ∈ [0,2])
    (d29 : a 29 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 17)=true)
    (c14 : edge r14 (a 2) (a 32)=true)
    (c18 : edge r18 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 11)=true)
    (c27 : edge r27 (a 6) (a 13)=true)
    (c29 : edge r29 (a 6) (a 35)=true)
    (c34 : edge r34 (a 8) (a 11)=true)
    (c35 : edge r35 (a 8) (a 22)=true)
    (c46 : edge r46 (a 11) (a 26)=true)
    (c47 : edge r47 (a 11) (a 41)=true)
    (c56 : edge r56 (a 15) (a 17)=true)
    (c64 : edge r64 (a 17) (a 24)=true)
    (c83 : edge r83 (a 24) (a 25)=true)
    (c86 : edge r86 (a 25) (a 29)=true)
    (c87 : edge r87 (a 25) (a 53)=true)
    : a 6 ∈ [1] ∧ a 17 ∈ [1] ∧ a 32 ∈ [2] ∧ a 4 ∈ [2] ∧ a 11 ∈ [1] ∧ a 13 ∈ [1] ∧ a 35 ∈ [1] ∧ a 8 ∈ [1] ∧ a 22 ∈ [2] ∧ a 26 ∈ [2] ∧ a 41 ∈ [2] ∧ a 15 ∈ [1] ∧ a 24 ∈ [2] ∧ a 25 ∈ [2] ∧ a 29 ∈ [1] ∧ a 53 ∈ [1] := by
  have b0 : a 6 ≠ 0 := exclude [2] (fun u v => edge r12 v u) (a 6) (a 2) 0 d2 c12 (by decide +kernel)
  have t0 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b0
  have b1 : a 17 ≠ 0 := exclude [2] (fun u v => edge r13 v u) (a 17) (a 2) 0 d2 c13 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 32 ≠ 0 := exclude [2] (fun u v => edge r14 v u) (a 32) (a 2) 0 d2 c14 (by decide +kernel)
  have t2 : a 32 ∈ [2] := remove (a 32) 0 [0,2] d32 b2
  have b3 : a 4 ≠ 0 := exclude [1] (edge r18) (a 4) (a 6) 0 t0 c18 (by decide +kernel)
  have t3 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b3
  have b4 : a 11 ≠ 0 := exclude [2] (fun u v => edge r19 v u) (a 11) (a 4) 0 t3 c19 (by decide +kernel)
  have t4 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b4
  have b5 : a 13 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 13) (a 6) 0 t0 c27 (by decide +kernel)
  have t5 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b5
  have b6 : a 35 ≠ 0 := exclude [1] (fun u v => edge r29 v u) (a 35) (a 6) 0 t0 c29 (by decide +kernel)
  have t6 : a 35 ∈ [1] := remove (a 35) 0 [0,1] d35 b6
  have b7 : a 8 ≠ 0 := exclude [1] (edge r34) (a 8) (a 11) 0 t4 c34 (by decide +kernel)
  have t7 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b7
  have b8 : a 22 ≠ 0 := exclude [1] (fun u v => edge r35 v u) (a 22) (a 8) 0 t7 c35 (by decide +kernel)
  have t8 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b8
  have b9 : a 26 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 26) (a 11) 0 t4 c46 (by decide +kernel)
  have t9 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b9
  have b10 : a 41 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 41) (a 11) 0 t4 c47 (by decide +kernel)
  have t10 : a 41 ∈ [2] := remove (a 41) 0 [0,2] d41 b10
  have b11 : a 15 ≠ 0 := exclude [1] (edge r56) (a 15) (a 17) 0 t1 c56 (by decide +kernel)
  have t11 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b11
  have b12 : a 24 ≠ 0 := exclude [1] (fun u v => edge r64 v u) (a 24) (a 17) 0 t1 c64 (by decide +kernel)
  have t12 : a 24 ∈ [2] := remove (a 24) 0 [0,2] d24 b12
  have b13 : a 25 ≠ 0 := exclude [2] (fun u v => edge r83 v u) (a 25) (a 24) 0 t12 c83 (by decide +kernel)
  have t13 : a 25 ∈ [2] := remove (a 25) 0 [0,2] d25 b13
  have b14 : a 29 ≠ 0 := exclude [2] (fun u v => edge r86 v u) (a 29) (a 25) 0 t13 c86 (by decide +kernel)
  have t14 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b14
  have b15 : a 53 ≠ 0 := exclude [2] (fun u v => edge r87 v u) (a 53) (a 25) 0 t13 c87 (by decide +kernel)
  have t15 : a 53 ∈ [1] := remove (a 53) 0 [0,1] d53 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_223
