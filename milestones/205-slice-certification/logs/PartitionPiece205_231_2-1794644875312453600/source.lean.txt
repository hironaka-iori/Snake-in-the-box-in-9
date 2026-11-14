import PartitionData205_231
namespace PartitionCover205_231
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1])
    (d14 : a 14 ∈ [2])
    (d30 : a 30 ∈ [0,1])
    (d15 : a 15 ∈ [2])
    (d44 : a 44 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [1])
    (d19 : a 19 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d22 : a 22 ∈ [1])
    (d26 : a 26 ∈ [0,2])
    (d56 : a 56 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d27 : a 27 ∈ [1])
    (d57 : a 57 ∈ [0,2])
    (d58 : a 58 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d33 : a 33 ∈ [2])
    (d32 : a 32 ∈ [0,1])
    (d35 : a 35 ∈ [2])
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
    : a 29 ∈ [1] ∧ a 30 ∈ [1] ∧ a 44 ∈ [1] ∧ a 16 ∈ [1] ∧ a 19 ∈ [2] ∧ a 21 ∈ [1] ∧ a 49 ∈ [1] ∧ a 52 ∈ [1] ∧ a 26 ∈ [2] ∧ a 56 ∈ [2] ∧ a 28 ∈ [1] ∧ a 57 ∈ [2] ∧ a 58 ∈ [1] ∧ a 31 ∈ [1] ∧ a 32 ∈ [1] ∧ a 39 ∈ [2] := by
  have b0 : a 29 ≠ 0 := exclude [2] (fun u v => edge r58 v u) (a 29) (a 14) 0 d14 c58 (by decide +kernel)
  have t0 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b0
  have b1 : a 30 ≠ 0 := exclude [2] (fun u v => edge r59 v u) (a 30) (a 15) 0 d15 c59 (by decide +kernel)
  have t1 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b1
  have b2 : a 44 ≠ 0 := exclude [2] (fun u v => edge r60 v u) (a 44) (a 15) 0 d15 c60 (by decide +kernel)
  have t2 : a 44 ∈ [1] := remove (a 44) 0 [0,1] d44 b2
  have b3 : a 16 ≠ 0 := exclude [1] (edge r62) (a 16) (a 18) 0 d18 c62 (by decide +kernel)
  have t3 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b3
  have b4 : a 19 ≠ 0 := exclude [1] (fun u v => edge r63 v u) (a 19) (a 16) 0 t3 c63 (by decide +kernel)
  have t4 : a 19 ∈ [2] := remove (a 19) 0 [0,2] d19 b4
  have b5 : a 21 ≠ 0 := exclude [1] (fun u v => edge r69 v u) (a 21) (a 18) 0 d18 c69 (by decide +kernel)
  have t5 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b5
  have b6 : a 49 ≠ 0 := exclude [2] (fun u v => edge r75 v u) (a 49) (a 19) 0 t4 c75 (by decide +kernel)
  have t6 : a 49 ∈ [1] := remove (a 49) 0 [0,1] d49 b6
  have b7 : a 52 ≠ 0 := exclude [1] (fun u v => edge r83 v u) (a 52) (a 22) 0 d22 c83 (by decide +kernel)
  have t7 : a 52 ∈ [1] := remove (a 52) 0 [0,1] d52 b7
  have b8 : a 26 ≠ 0 := exclude [1] (edge r94) (a 26) (a 30) 0 t1 c94 (by decide +kernel)
  have t8 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b8
  have b9 : a 56 ≠ 0 := exclude [2] (fun u v => edge r95 v u) (a 56) (a 26) 0 t8 c95 (by decide +kernel)
  have t9 : a 56 ∈ [2] := remove (a 56) 0 [0,2] d56 b9
  have b10 : a 28 ≠ 0 := exclude [1] (fun u v => edge r96 v u) (a 28) (a 27) 0 d27 c96 (by decide +kernel)
  have t10 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b10
  have b11 : a 57 ≠ 0 := exclude [1] (fun u v => edge r99 v u) (a 57) (a 28) 0 t10 c99 (by decide +kernel)
  have t11 : a 57 ∈ [2] := remove (a 57) 0 [0,2] d57 b11
  have b12 : a 58 ≠ 0 := exclude [1] (fun u v => edge r101 v u) (a 58) (a 29) 0 t0 c101 (by decide +kernel)
  have t12 : a 58 ∈ [1] := remove (a 58) 0 [0,1] d58 b12
  have b13 : a 31 ≠ 0 := exclude [2] (edge r104) (a 31) (a 33) 0 d33 c104 (by decide +kernel)
  have t13 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b13
  have b14 : a 32 ≠ 0 := exclude [2] (edge r108) (a 32) (a 35) 0 d35 c108 (by decide +kernel)
  have t14 : a 32 ∈ [1] := remove (a 32) 0 [0,1] d32 b14
  have b15 : a 39 ≠ 0 := exclude [1] (fun u v => edge r109 v u) (a 39) (a 32) 0 t14 c109 (by decide +kernel)
  have t15 : a 39 ∈ [2] := remove (a 39) 0 [0,2] d39 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d46 : a 46 ∈ [0,1])
    (d32 : a 32 ∈ [1])
    (d43 : a 43 ∈ [0,1])
    (d35 : a 35 ∈ [2])
    (d50 : a 50 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d39 : a 39 ∈ [2])
    (d54 : a 54 ∈ [0,2])
    (d55 : a 55 ∈ [0,1])
    (d40 : a 40 ∈ [2])
    (d48 : a 48 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d5 : a 5 ∈ [1])
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [2])
    (d24 : a 24 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d16 : a 16 ∈ [1])
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
    : a 46 ∈ [1] ∧ a 43 ∈ [1] ∧ a 50 ∈ [1] ∧ a 41 ∈ [1] ∧ a 54 ∈ [2] ∧ a 55 ∈ [1] ∧ a 48 ∈ [1] ∧ a 53 ∈ [1] ∧ a 4 ∈ [2] ∧ a 9 ∈ [1] ∧ a 24 ∈ [1] ∧ a 17 ∈ [1] := by
  have b0 : a 46 ≠ 0 := exclude [1] (fun u v => edge r110 v u) (a 46) (a 32) 0 d32 c110 (by decide +kernel)
  have t0 : a 46 ∈ [1] := remove (a 46) 0 [0,1] d46 b0
  have b1 : a 43 ≠ 0 := exclude [2] (fun u v => edge r119 v u) (a 43) (a 35) 0 d35 c119 (by decide +kernel)
  have t1 : a 43 ∈ [1] := remove (a 43) 0 [0,1] d43 b1
  have b2 : a 50 ≠ 0 := exclude [2] (fun u v => edge r120 v u) (a 50) (a 35) 0 d35 c120 (by decide +kernel)
  have t2 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b2
  have b3 : a 41 ≠ 0 := exclude [2] (fun u v => edge r129 v u) (a 41) (a 39) 0 d39 c129 (by decide +kernel)
  have t3 : a 41 ∈ [1] := remove (a 41) 0 [0,1] d41 b3
  have b4 : a 54 ≠ 0 := exclude [2] (fun u v => edge r131 v u) (a 54) (a 39) 0 d39 c131 (by decide +kernel)
  have t4 : a 54 ∈ [2] := remove (a 54) 0 [0,2] d54 b4
  have b5 : a 55 ≠ 0 := exclude [2] (fun u v => edge r133 v u) (a 55) (a 40) 0 d40 c133 (by decide +kernel)
  have t5 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b5
  have b6 : a 48 ≠ 0 := exclude [1] (fun u v => edge r144 v u) (a 48) (a 46) 0 t0 c144 (by decide +kernel)
  have t6 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b6
  have b7 : a 53 ≠ 0 := exclude [2] (edge r159) (a 53) (a 54) 0 t4 c159 (by decide +kernel)
  have t7 : a 53 ∈ [1] := remove (a 53) 0 [0,1] d53 b7
  have b8 : a 4 ≠ 0 := exclude [1] (edge r18) (a 4) (a 5) 0 d5 c18 (by decide +kernel)
  have t8 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b8
  have b9 : a 9 ≠ 0 := exclude [2] (fun u v => edge r34 v u) (a 9) (a 8) 0 d8 c34 (by decide +kernel)
  have t9 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b9
  have b10 : a 24 ≠ 0 := exclude [1] (fun u v => edge r41 v u) (a 24) (a 9) 0 t9 c41 (by decide +kernel)
  have t10 : a 24 ∈ [1] := remove (a 24) 0 [0,1] d24 b10
  have b11 : a 17 ≠ 0 := exclude [1] (fun u v => edge r61 v u) (a 17) (a 16) 0 d16 c61 (by decide +kernel)
  have t11 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b11
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t11)))))))))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_231
