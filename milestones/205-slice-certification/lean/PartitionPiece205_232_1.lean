import PartitionData205_232
namespace PartitionCover205_232
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d40 : a 40 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d32 : a 32 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d33 : a 33 ∈ [0])
    (d34 : a 34 ∈ [0,1])
    (c41 : edge r41 (a 10) (a 40)=true)
    (c50 : edge r50 (a 14) (a 15)=true)
    (c98 : edge r98 (a 30) (a 32)=true)
    (c101 : edge r101 (a 31) (a 33)=true)
    (c104 : edge r104 (a 32) (a 34)=true)
    : a 40 ∈ [0] ∧ a 14 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 34 ∈ [0] := by
  have b0 : a 40 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 40) (a 10) 1 d10 c41 (by decide +kernel)
  have t0 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b0
  have b1 : a 14 ≠ 1 := exclude [0] (edge r50) (a 14) (a 15) 1 d15 c50 (by decide +kernel)
  have t1 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b1
  have b2 : a 30 ≠ 1 := exclude [0] (edge r98) (a 30) (a 32) 1 d32 c98 (by decide +kernel)
  have t2 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b2
  have b3 : a 31 ≠ 1 := exclude [0] (edge r101) (a 31) (a 33) 1 d33 c101 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b3
  have b4 : a 34 ≠ 1 := exclude [0] (fun u v => edge r104 v u) (a 34) (a 32) 1 d32 c104 (by decide +kernel)
  have t4 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))

theorem chunk5 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d39 : a 39 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d16 : a 16 ∈ [0,2])
    (d46 : a 46 ∈ [0,2])
    (d21 : a 21 ∈ [0,2])
    (d18 : a 18 ∈ [0,1])
    (c10 : edge r10 (a 2) (a 9)=true)
    (c11 : edge r11 (a 2) (a 17)=true)
    (c27 : edge r27 (a 7) (a 9)=true)
    (c31 : edge r31 (a 8) (a 9)=true)
    (c33 : edge r33 (a 8) (a 24)=true)
    (c35 : edge r35 (a 9) (a 13)=true)
    (c36 : edge r36 (a 9) (a 25)=true)
    (c37 : edge r37 (a 9) (a 39)=true)
    (c48 : edge r48 (a 13) (a 29)=true)
    (c49 : edge r49 (a 13) (a 43)=true)
    (c55 : edge r55 (a 15) (a 17)=true)
    (c56 : edge r56 (a 15) (a 19)=true)
    (c59 : edge r59 (a 16) (a 17)=true)
    (c62 : edge r62 (a 16) (a 46)=true)
    (c63 : edge r63 (a 17) (a 21)=true)
    (c66 : edge r66 (a 18) (a 19)=true)
    : a 9 ∈ [1] ∧ a 17 ∈ [1] ∧ a 7 ∈ [1] ∧ a 8 ∈ [1] ∧ a 24 ∈ [1] ∧ a 13 ∈ [1] ∧ a 25 ∈ [1] ∧ a 39 ∈ [1] ∧ a 29 ∈ [1] ∧ a 43 ∈ [1] ∧ a 15 ∈ [1] ∧ a 19 ∈ [1] ∧ a 16 ∈ [2] ∧ a 46 ∈ [2] ∧ a 21 ∈ [2] ∧ a 18 ∈ [1] := by
  have b0 : a 9 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 9) (a 2) 0 d2 c10 (by decide +kernel)
  have t0 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b0
  have b1 : a 17 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 17) (a 2) 0 d2 c11 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 7 ≠ 0 := exclude [1] (edge r27) (a 7) (a 9) 0 t0 c27 (by decide +kernel)
  have t2 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b2
  have b3 : a 8 ≠ 0 := exclude [1] (edge r31) (a 8) (a 9) 0 t0 c31 (by decide +kernel)
  have t3 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b3
  have b4 : a 24 ≠ 0 := exclude [1] (fun u v => edge r33 v u) (a 24) (a 8) 0 t3 c33 (by decide +kernel)
  have t4 : a 24 ∈ [1] := remove (a 24) 0 [0,1] d24 b4
  have b5 : a 13 ≠ 0 := exclude [1] (fun u v => edge r35 v u) (a 13) (a 9) 0 t0 c35 (by decide +kernel)
  have t5 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b5
  have b6 : a 25 ≠ 0 := exclude [1] (fun u v => edge r36 v u) (a 25) (a 9) 0 t0 c36 (by decide +kernel)
  have t6 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b6
  have b7 : a 39 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 39) (a 9) 0 t0 c37 (by decide +kernel)
  have t7 : a 39 ∈ [1] := remove (a 39) 0 [0,1] d39 b7
  have b8 : a 29 ≠ 0 := exclude [1] (fun u v => edge r48 v u) (a 29) (a 13) 0 t5 c48 (by decide +kernel)
  have t8 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b8
  have b9 : a 43 ≠ 0 := exclude [1] (fun u v => edge r49 v u) (a 43) (a 13) 0 t5 c49 (by decide +kernel)
  have t9 : a 43 ∈ [1] := remove (a 43) 0 [0,1] d43 b9
  have b10 : a 15 ≠ 0 := exclude [1] (edge r55) (a 15) (a 17) 0 t1 c55 (by decide +kernel)
  have t10 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b10
  have b11 : a 19 ≠ 0 := exclude [1] (fun u v => edge r56 v u) (a 19) (a 15) 0 t10 c56 (by decide +kernel)
  have t11 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b11
  have b12 : a 16 ≠ 0 := exclude [1] (edge r59) (a 16) (a 17) 0 t1 c59 (by decide +kernel)
  have t12 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b12
  have b13 : a 46 ≠ 0 := exclude [2] (fun u v => edge r62 v u) (a 46) (a 16) 0 t12 c62 (by decide +kernel)
  have t13 : a 46 ∈ [2] := remove (a 46) 0 [0,2] d46 b13
  have b14 : a 21 ≠ 0 := exclude [1] (fun u v => edge r63 v u) (a 21) (a 17) 0 t1 c63 (by decide +kernel)
  have t14 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b14
  have b15 : a 18 ≠ 0 := exclude [1] (edge r66) (a 18) (a 19) 0 t11 c66 (by decide +kernel)
  have t15 : a 18 ∈ [1] := remove (a 18) 0 [0,1] d18 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1])
    (d18 : a 18 ∈ [1])
    (d48 : a 48 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d24 : a 24 ∈ [1])
    (d54 : a 54 ∈ [0,2])
    (d55 : a 55 ∈ [0,1])
    (d25 : a 25 ∈ [1])
    (d57 : a 57 ∈ [0,2])
    (d32 : a 32 ∈ [0,1])
    (d46 : a 46 ∈ [2])
    (d35 : a 35 ∈ [0,1])
    (d43 : a 43 ∈ [1])
    (d50 : a 50 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d56 : a 56 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d19 : a 19 ∈ [1])
    (d33 : a 33 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [1])
    (d10 : a 10 ∈ [0,1])
    (c17 : edge r17 (a 4) (a 19)=true)
    (c18 : edge r18 (a 4) (a 33)=true)
    (c22 : edge r22 (a 6) (a 7)=true)
    (c24 : edge r24 (a 6) (a 10)=true)
    (c68 : edge r68 (a 18) (a 26)=true)
    (c69 : edge r69 (a 18) (a 48)=true)
    (c86 : edge r86 (a 24) (a 28)=true)
    (c87 : edge r87 (a 24) (a 54)=true)
    (c89 : edge r89 (a 25) (a 55)=true)
    (c95 : edge r95 (a 28) (a 57)=true)
    (c106 : edge r106 (a 32) (a 46)=true)
    (c113 : edge r113 (a 35) (a 43)=true)
    (c142 : edge r142 (a 46) (a 50)=true)
    (c154 : edge r154 (a 52) (a 54)=true)
    (c155 : edge r155 (a 53) (a 55)=true)
    (c156 : edge r156 (a 53) (a 56)=true)
    : a 26 ∈ [1] ∧ a 48 ∈ [2] ∧ a 28 ∈ [1] ∧ a 54 ∈ [2] ∧ a 55 ∈ [1] ∧ a 57 ∈ [2] ∧ a 32 ∈ [1] ∧ a 35 ∈ [1] ∧ a 50 ∈ [1] ∧ a 52 ∈ [1] ∧ a 53 ∈ [1] ∧ a 56 ∈ [2] ∧ a 4 ∈ [1] ∧ a 33 ∈ [1] ∧ a 6 ∈ [1] ∧ a 10 ∈ [1] := by
  have b0 : a 26 ≠ 0 := exclude [1] (fun u v => edge r68 v u) (a 26) (a 18) 0 d18 c68 (by decide +kernel)
  have t0 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b0
  have b1 : a 48 ≠ 0 := exclude [1] (fun u v => edge r69 v u) (a 48) (a 18) 0 d18 c69 (by decide +kernel)
  have t1 : a 48 ∈ [2] := remove (a 48) 0 [0,2] d48 b1
  have b2 : a 28 ≠ 0 := exclude [1] (fun u v => edge r86 v u) (a 28) (a 24) 0 d24 c86 (by decide +kernel)
  have t2 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b2
  have b3 : a 54 ≠ 0 := exclude [1] (fun u v => edge r87 v u) (a 54) (a 24) 0 d24 c87 (by decide +kernel)
  have t3 : a 54 ∈ [2] := remove (a 54) 0 [0,2] d54 b3
  have b4 : a 55 ≠ 0 := exclude [1] (fun u v => edge r89 v u) (a 55) (a 25) 0 d25 c89 (by decide +kernel)
  have t4 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b4
  have b5 : a 57 ≠ 0 := exclude [1] (fun u v => edge r95 v u) (a 57) (a 28) 0 t2 c95 (by decide +kernel)
  have t5 : a 57 ∈ [2] := remove (a 57) 0 [0,2] d57 b5
  have b6 : a 32 ≠ 0 := exclude [2] (edge r106) (a 32) (a 46) 0 d46 c106 (by decide +kernel)
  have t6 : a 32 ∈ [1] := remove (a 32) 0 [0,1] d32 b6
  have b7 : a 35 ≠ 0 := exclude [1] (edge r113) (a 35) (a 43) 0 d43 c113 (by decide +kernel)
  have t7 : a 35 ∈ [1] := remove (a 35) 0 [0,1] d35 b7
  have b8 : a 50 ≠ 0 := exclude [2] (fun u v => edge r142 v u) (a 50) (a 46) 0 d46 c142 (by decide +kernel)
  have t8 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b8
  have b9 : a 52 ≠ 0 := exclude [2] (edge r154) (a 52) (a 54) 0 t3 c154 (by decide +kernel)
  have t9 : a 52 ∈ [1] := remove (a 52) 0 [0,1] d52 b9
  have b10 : a 53 ≠ 0 := exclude [1] (edge r155) (a 53) (a 55) 0 t4 c155 (by decide +kernel)
  have t10 : a 53 ∈ [1] := remove (a 53) 0 [0,1] d53 b10
  have b11 : a 56 ≠ 0 := exclude [1] (fun u v => edge r156 v u) (a 56) (a 53) 0 t10 c156 (by decide +kernel)
  have t11 : a 56 ∈ [2] := remove (a 56) 0 [0,2] d56 b11
  have b12 : a 4 ≠ 0 := exclude [1] (edge r17) (a 4) (a 19) 0 d19 c17 (by decide +kernel)
  have t12 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b12
  have b13 : a 33 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 33) (a 4) 0 t12 c18 (by decide +kernel)
  have t13 : a 33 ∈ [1] := remove (a 33) 0 [0,1] d33 b13
  have b14 : a 6 ≠ 0 := exclude [1] (edge r22) (a 6) (a 7) 0 d7 c22 (by decide +kernel)
  have t14 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b14
  have b15 : a 10 ≠ 0 := exclude [1] (fun u v => edge r24 v u) (a 10) (a 6) 0 t14 c24 (by decide +kernel)
  have t15 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk7 (a : Nat → Nat)
    (d40 : a 40 ∈ [0,1])
    (d10 : a 10 ∈ [1])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d32 : a 32 ∈ [1])
    (d31 : a 31 ∈ [0,1])
    (d33 : a 33 ∈ [1])
    (d34 : a 34 ∈ [0,1])
    (c41 : edge r41 (a 10) (a 40)=true)
    (c50 : edge r50 (a 14) (a 15)=true)
    (c98 : edge r98 (a 30) (a 32)=true)
    (c101 : edge r101 (a 31) (a 33)=true)
    (c104 : edge r104 (a 32) (a 34)=true)
    : a 40 ∈ [1] ∧ a 14 ∈ [1] ∧ a 30 ∈ [1] ∧ a 31 ∈ [1] ∧ a 34 ∈ [1] := by
  have b0 : a 40 ≠ 0 := exclude [1] (fun u v => edge r41 v u) (a 40) (a 10) 0 d10 c41 (by decide +kernel)
  have t0 : a 40 ∈ [1] := remove (a 40) 0 [0,1] d40 b0
  have b1 : a 14 ≠ 0 := exclude [1] (edge r50) (a 14) (a 15) 0 d15 c50 (by decide +kernel)
  have t1 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b1
  have b2 : a 30 ≠ 0 := exclude [1] (edge r98) (a 30) (a 32) 0 d32 c98 (by decide +kernel)
  have t2 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b2
  have b3 : a 31 ≠ 0 := exclude [1] (edge r101) (a 31) (a 33) 0 d33 c101 (by decide +kernel)
  have t3 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b3
  have b4 : a 34 ≠ 0 := exclude [1] (fun u v => edge r104 v u) (a 34) (a 32) 0 d32 c104 (by decide +kernel)
  have t4 : a 34 ∈ [1] := remove (a 34) 0 [0,1] d34 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))
#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_232
