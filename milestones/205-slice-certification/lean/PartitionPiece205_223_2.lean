import PartitionData205_223
namespace PartitionCover205_223
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1])
    (d26 : a 26 ∈ [2])
    (d54 : a 54 ∈ [0,2])
    (d57 : a 57 ∈ [0,2])
    (d29 : a 29 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d32 : a 32 ∈ [2])
    (d36 : a 36 ∈ [0,1])
    (d35 : a 35 ∈ [1])
    (d50 : a 50 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d41 : a 41 ∈ [2])
    (d47 : a 47 ∈ [0,1])
    (d53 : a 53 ∈ [1])
    (d48 : a 48 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d51 : a 51 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [2])
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
    : a 27 ∈ [1] ∧ a 54 ∈ [2] ∧ a 57 ∈ [2] ∧ a 30 ∈ [1] ∧ a 36 ∈ [1] ∧ a 50 ∈ [1] ∧ a 43 ∈ [1] ∧ a 40 ∈ [1] ∧ a 42 ∈ [1] ∧ a 47 ∈ [1] ∧ a 48 ∈ [1] ∧ a 56 ∈ [1] ∧ a 51 ∈ [2] ∧ a 5 ∈ [1] ∧ a 19 ∈ [1] ∧ a 34 ∈ [2] := by
  have b0 : a 27 ≠ 0 := exclude [2] (fun u v => edge r88 v u) (a 27) (a 26) 0 d26 c88 (by decide +kernel)
  have t0 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b0
  have b1 : a 54 ≠ 0 := exclude [2] (fun u v => edge r90 v u) (a 54) (a 26) 0 d26 c90 (by decide +kernel)
  have t1 : a 54 ∈ [2] := remove (a 54) 0 [0,2] d54 b1
  have b2 : a 57 ≠ 0 := exclude [1] (fun u v => edge r95 v u) (a 57) (a 29) 0 d29 c95 (by decide +kernel)
  have t2 : a 57 ∈ [2] := remove (a 57) 0 [0,2] d57 b2
  have b3 : a 30 ≠ 0 := exclude [2] (edge r97) (a 30) (a 32) 0 d32 c97 (by decide +kernel)
  have t3 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b3
  have b4 : a 36 ≠ 0 := exclude [1] (fun u v => edge r114 v u) (a 36) (a 35) 0 d35 c114 (by decide +kernel)
  have t4 : a 36 ∈ [1] := remove (a 36) 0 [0,1] d36 b4
  have b5 : a 50 ≠ 0 := exclude [1] (fun u v => edge r115 v u) (a 50) (a 35) 0 d35 c115 (by decide +kernel)
  have t5 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b5
  have b6 : a 43 ≠ 0 := exclude [1] (fun u v => edge r116 v u) (a 43) (a 36) 0 t4 c116 (by decide +kernel)
  have t6 : a 43 ∈ [1] := remove (a 43) 0 [0,1] d43 b6
  have b7 : a 40 ≠ 0 := exclude [1] (edge r125) (a 40) (a 43) 0 t6 c125 (by decide +kernel)
  have t7 : a 40 ∈ [1] := remove (a 40) 0 [0,1] d40 b7
  have b8 : a 42 ≠ 0 := exclude [2] (fun u v => edge r127 v u) (a 42) (a 41) 0 d41 c127 (by decide +kernel)
  have t8 : a 42 ∈ [1] := remove (a 42) 0 [0,1] d42 b8
  have b9 : a 47 ≠ 0 := exclude [1] (edge r141) (a 47) (a 53) 0 d53 c141 (by decide +kernel)
  have t9 : a 47 ∈ [1] := remove (a 47) 0 [0,1] d47 b9
  have b10 : a 48 ≠ 0 := exclude [1] (edge r143) (a 48) (a 50) 0 t5 c143 (by decide +kernel)
  have t10 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b10
  have b11 : a 56 ≠ 0 := exclude [1] (fun u v => edge r146 v u) (a 56) (a 50) 0 t5 c146 (by decide +kernel)
  have t11 : a 56 ∈ [1] := remove (a 56) 0 [0,1] d56 b11
  have b12 : a 51 ≠ 0 := exclude [1] (edge r147) (a 51) (a 53) 0 d53 c147 (by decide +kernel)
  have t12 : a 51 ∈ [2] := remove (a 51) 0 [0,2] d51 b12
  have b13 : a 5 ≠ 0 := exclude [2] (fun u v => edge r17 v u) (a 5) (a 4) 0 d4 c17 (by decide +kernel)
  have t13 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b13
  have b14 : a 19 ≠ 0 := exclude [1] (fun u v => edge r24 v u) (a 19) (a 5) 0 t13 c24 (by decide +kernel)
  have t14 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b14
  have b15 : a 34 ≠ 0 := exclude [1] (fun u v => edge r25 v u) (a 34) (a 5) 0 t13 c25 (by decide +kernel)
  have t15 : a 34 ∈ [2] := remove (a 34) 0 [0,2] d34 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d8 : a 8 ∈ [1])
    (d10 : a 10 ∈ [0,1])
    (d38 : a 38 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d15 : a 15 ∈ [1])
    (d45 : a 45 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d19 : a 19 ∈ [1])
    (d49 : a 49 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d30 : a 30 ∈ [1])
    (c33 : edge r33 (a 8) (a 9)=true)
    (c37 : edge r37 (a 9) (a 10)=true)
    (c40 : edge r40 (a 9) (a 38)=true)
    (c55 : edge r55 (a 15) (a 16)=true)
    (c62 : edge r62 (a 16) (a 45)=true)
    (c70 : edge r70 (a 19) (a 21)=true)
    (c72 : edge r72 (a 19) (a 49)=true)
    (c96 : edge r96 (a 30) (a 31)=true)
    : a 9 ∈ [1] ∧ a 10 ∈ [1] ∧ a 38 ∈ [1] ∧ a 16 ∈ [1] ∧ a 45 ∈ [1] ∧ a 21 ∈ [1] ∧ a 49 ∈ [2] ∧ a 31 ∈ [1] := by
  have b0 : a 9 ≠ 0 := exclude [1] (fun u v => edge r33 v u) (a 9) (a 8) 0 d8 c33 (by decide +kernel)
  have t0 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b0
  have b1 : a 10 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 10) (a 9) 0 t0 c37 (by decide +kernel)
  have t1 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b1
  have b2 : a 38 ≠ 0 := exclude [1] (fun u v => edge r40 v u) (a 38) (a 9) 0 t0 c40 (by decide +kernel)
  have t2 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b2
  have b3 : a 16 ≠ 0 := exclude [1] (fun u v => edge r55 v u) (a 16) (a 15) 0 d15 c55 (by decide +kernel)
  have t3 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b3
  have b4 : a 45 ≠ 0 := exclude [1] (fun u v => edge r62 v u) (a 45) (a 16) 0 t3 c62 (by decide +kernel)
  have t4 : a 45 ∈ [1] := remove (a 45) 0 [0,1] d45 b4
  have b5 : a 21 ≠ 0 := exclude [1] (fun u v => edge r70 v u) (a 21) (a 19) 0 d19 c70 (by decide +kernel)
  have t5 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b5
  have b6 : a 49 ≠ 0 := exclude [1] (fun u v => edge r72 v u) (a 49) (a 19) 0 d19 c72 (by decide +kernel)
  have t6 : a 49 ∈ [2] := remove (a 49) 0 [0,2] d49 b6
  have b7 : a 31 ≠ 0 := exclude [1] (fun u v => edge r96 v u) (a 31) (a 30) 0 d30 c96 (by decide +kernel)
  have t7 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_223
