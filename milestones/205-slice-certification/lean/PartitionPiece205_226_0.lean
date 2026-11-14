import PartitionData205_226
namespace PartitionCover205_226
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0,1])
    (d13 : a 13 ∈ [0,1,2,3])
    (d47 : a 47 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1])
    (d57 : a 57 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0])
    (d55 : a 55 ∈ [0,1,2,3])
    (d40 : a 40 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d48 : a 48 ∈ [0,1,2,3])
    (d53 : a 53 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (c22 : edge r22 (a 5) (a 6)=true)
    (c23 : edge r23 (a 5) (a 13)=true)
    (c68 : edge r68 (a 17) (a 47)=true)
    (c96 : edge r96 (a 28) (a 57)=true)
    (c131 : edge r131 (a 40) (a 55)=true)
    (c140 : edge r140 (a 45) (a 46)=true)
    (c141 : edge r141 (a 45) (a 47)=true)
    (c146 : edge r146 (a 47) (a 48)=true)
    (c159 : edge r159 (a 53) (a 55)=true)
    : a 5 ∈ [0,2] ∧ a 13 ∈ [0,2] ∧ a 47 ∈ [0,2] ∧ a 57 ∈ [0,2] ∧ a 55 ∈ [0,1] ∧ a 45 ∈ [0] ∧ a 48 ∈ [0,1] ∧ a 53 ∈ [0] ∧ a 46 ∈ [0] := by
  have b0 : a 5 ≠ 1 := exclude [0,1] (edge r22) (a 5) (a 6) 1 d6 c22 (by decide +kernel)
  have t0 : a 5 ∈ [0,2,3] := remove (a 5) 1 [0,1,2,3] d5 b0
  have b1 : a 5 ≠ 3 := exclude [0,1] (edge r22) (a 5) (a 6) 3 d6 c22 (by decide +kernel)
  have t1 : a 5 ∈ [0,2] := remove (a 5) 3 [0,2,3] t0 b1
  have b2 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r23 v u) (a 13) (a 5) 1 t1 c23 (by decide +kernel)
  have t2 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b2
  have b3 : a 13 ≠ 3 := exclude [0,2] (fun u v => edge r23 v u) (a 13) (a 5) 3 t1 c23 (by decide +kernel)
  have t3 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t2 b3
  have b4 : a 47 ≠ 1 := exclude [0,1] (fun u v => edge r68 v u) (a 47) (a 17) 1 d17 c68 (by decide +kernel)
  have t4 : a 47 ∈ [0,2,3] := remove (a 47) 1 [0,1,2,3] d47 b4
  have b5 : a 47 ≠ 3 := exclude [0,1] (fun u v => edge r68 v u) (a 47) (a 17) 3 d17 c68 (by decide +kernel)
  have t5 : a 47 ∈ [0,2] := remove (a 47) 3 [0,2,3] t4 b5
  have b6 : a 57 ≠ 1 := exclude [0] (fun u v => edge r96 v u) (a 57) (a 28) 1 d28 c96 (by decide +kernel)
  have t6 : a 57 ∈ [0,2,3] := remove (a 57) 1 [0,1,2,3] d57 b6
  have b7 : a 57 ≠ 3 := exclude [0] (fun u v => edge r96 v u) (a 57) (a 28) 3 d28 c96 (by decide +kernel)
  have t7 : a 57 ∈ [0,2] := remove (a 57) 3 [0,2,3] t6 b7
  have b8 : a 55 ≠ 2 := exclude [0,1] (fun u v => edge r131 v u) (a 55) (a 40) 2 d40 c131 (by decide +kernel)
  have t8 : a 55 ∈ [0,1,3] := remove (a 55) 2 [0,1,2,3] d55 b8
  have b9 : a 55 ≠ 3 := exclude [0,1] (fun u v => edge r131 v u) (a 55) (a 40) 3 d40 c131 (by decide +kernel)
  have t9 : a 55 ∈ [0,1] := remove (a 55) 3 [0,1,3] t8 b9
  have b10 : a 45 ≠ 1 := exclude [0,2] (edge r141) (a 45) (a 47) 1 t5 c141 (by decide +kernel)
  have t10 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b10
  have b11 : a 48 ≠ 2 := exclude [0,2] (fun u v => edge r146 v u) (a 48) (a 47) 2 t5 c146 (by decide +kernel)
  have t11 : a 48 ∈ [0,1,3] := remove (a 48) 2 [0,1,2,3] d48 b11
  have b12 : a 48 ≠ 3 := exclude [0,2] (fun u v => edge r146 v u) (a 48) (a 47) 3 t5 c146 (by decide +kernel)
  have t12 : a 48 ∈ [0,1] := remove (a 48) 3 [0,1,3] t11 b12
  have b13 : a 53 ≠ 1 := exclude [0,1] (edge r159) (a 53) (a 55) 1 t9 c159 (by decide +kernel)
  have t13 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b13
  have b14 : a 46 ≠ 1 := exclude [0] (fun u v => edge r140 v u) (a 46) (a 45) 1 t10 c140 (by decide +kernel)
  have t14 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b14
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (t14))))))))

theorem chunk1 (a : Nat → Nat)
    (d4 : a 4 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d39 : a 39 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d44 : a 44 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d47 : a 47 ∈ [0,2])
    (c13 : edge r13 (a 3) (a 4)=true)
    (c14 : edge r14 (a 3) (a 5)=true)
    (c15 : edge r15 (a 3) (a 11)=true)
    (c18 : edge r18 (a 4) (a 6)=true)
    (c23 : edge r23 (a 5) (a 13)=true)
    (c24 : edge r24 (a 5) (a 21)=true)
    (c26 : edge r26 (a 6) (a 14)=true)
    (c27 : edge r27 (a 6) (a 22)=true)
    (c28 : edge r28 (a 6) (a 36)=true)
    (c39 : edge r39 (a 9) (a 13)=true)
    (c41 : edge r41 (a 9) (a 39)=true)
    (c47 : edge r47 (a 11) (a 27)=true)
    (c54 : edge r54 (a 14) (a 29)=true)
    (c55 : edge r55 (a 14) (a 44)=true)
    (c66 : edge r66 (a 17) (a 21)=true)
    (c68 : edge r68 (a 17) (a 47)=true)
    : a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 11 ∈ [0] ∧ a 6 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 36 ∈ [0] ∧ a 9 ∈ [0] ∧ a 39 ∈ [0] ∧ a 27 ∈ [0] ∧ a 29 ∈ [0] ∧ a 44 ∈ [0] ∧ a 17 ∈ [0] ∧ a 47 ∈ [0] := by
  have b0 : a 4 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 4) (a 3) 1 d3 c13 (by decide +kernel)
  have t0 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b0
  have b1 : a 5 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 5) (a 3) 2 d3 c14 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b1
  have b2 : a 11 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 11) (a 3) 1 d3 c15 (by decide +kernel)
  have t2 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b2
  have b3 : a 6 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 6) (a 4) 1 t0 c18 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b3
  have b4 : a 13 ≠ 2 := exclude [0] (fun u v => edge r23 v u) (a 13) (a 5) 2 t1 c23 (by decide +kernel)
  have t4 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b4
  have b5 : a 21 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 21) (a 5) 1 t1 c24 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b5
  have b6 : a 14 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 14) (a 6) 1 t3 c26 (by decide +kernel)
  have t6 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b6
  have b7 : a 22 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 22) (a 6) 1 t3 c27 (by decide +kernel)
  have t7 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b7
  have b8 : a 36 ≠ 1 := exclude [0] (fun u v => edge r28 v u) (a 36) (a 6) 1 t3 c28 (by decide +kernel)
  have t8 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b8
  have b9 : a 9 ≠ 1 := exclude [0] (edge r39) (a 9) (a 13) 1 t4 c39 (by decide +kernel)
  have t9 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b9
  have b10 : a 39 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 39) (a 9) 1 t9 c41 (by decide +kernel)
  have t10 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b10
  have b11 : a 27 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 27) (a 11) 1 t2 c47 (by decide +kernel)
  have t11 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b11
  have b12 : a 29 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 29) (a 14) 1 t6 c54 (by decide +kernel)
  have t12 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b12
  have b13 : a 44 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 44) (a 14) 1 t6 c55 (by decide +kernel)
  have t13 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b13
  have b14 : a 17 ≠ 1 := exclude [0] (edge r66) (a 17) (a 21) 1 t5 c66 (by decide +kernel)
  have t14 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b14
  have b15 : a 47 ≠ 2 := exclude [0] (fun u v => edge r68 v u) (a 47) (a 17) 2 t14 c68 (by decide +kernel)
  have t15 : a 47 ∈ [0] := remove (a 47) 2 [0,2] d47 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk2 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d52 : a 52 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d59 : a 59 ∈ [0,1])
    (d29 : a 29 ∈ [0])
    (d32 : a 32 ∈ [0,1])
    (d39 : a 39 ∈ [0])
    (d40 : a 40 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d50 : a 50 ∈ [0,1])
    (d57 : a 57 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (c36 : edge r36 (a 8) (a 24)=true)
    (c69 : edge r69 (a 18) (a 22)=true)
    (c70 : edge r70 (a 18) (a 26)=true)
    (c71 : edge r71 (a 18) (a 48)=true)
    (c80 : edge r80 (a 21) (a 51)=true)
    (c82 : edge r82 (a 22) (a 52)=true)
    (c85 : edge r85 (a 23) (a 27)=true)
    (c86 : edge r86 (a 24) (a 26)=true)
    (c92 : edge r92 (a 26) (a 55)=true)
    (c94 : edge r94 (a 27) (a 56)=true)
    (c97 : edge r97 (a 29) (a 59)=true)
    (c107 : edge r107 (a 32) (a 39)=true)
    (c127 : edge r127 (a 39) (a 40)=true)
    (c152 : edge r152 (a 49) (a 51)=true)
    (c154 : edge r154 (a 50) (a 52)=true)
    (c155 : edge r155 (a 50) (a 57)=true)
    : a 18 ∈ [0] ∧ a 26 ∈ [0] ∧ a 48 ∈ [0] ∧ a 51 ∈ [0] ∧ a 52 ∈ [0] ∧ a 23 ∈ [0] ∧ a 24 ∈ [0] ∧ a 55 ∈ [0] ∧ a 56 ∈ [0] ∧ a 59 ∈ [0] ∧ a 32 ∈ [0] ∧ a 40 ∈ [0] ∧ a 49 ∈ [0] ∧ a 50 ∈ [0] ∧ a 57 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 18 ≠ 1 := exclude [0] (edge r69) (a 18) (a 22) 1 d22 c69 (by decide +kernel)
  have t0 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b0
  have b1 : a 26 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 26) (a 18) 1 t0 c70 (by decide +kernel)
  have t1 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b1
  have b2 : a 48 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 48) (a 18) 1 t0 c71 (by decide +kernel)
  have t2 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b2
  have b3 : a 51 ≠ 1 := exclude [0] (fun u v => edge r80 v u) (a 51) (a 21) 1 d21 c80 (by decide +kernel)
  have t3 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b3
  have b4 : a 52 ≠ 1 := exclude [0] (fun u v => edge r82 v u) (a 52) (a 22) 1 d22 c82 (by decide +kernel)
  have t4 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b4
  have b5 : a 23 ≠ 1 := exclude [0] (edge r85) (a 23) (a 27) 1 d27 c85 (by decide +kernel)
  have t5 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b5
  have b6 : a 24 ≠ 1 := exclude [0] (edge r86) (a 24) (a 26) 1 t1 c86 (by decide +kernel)
  have t6 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b6
  have b7 : a 55 ≠ 1 := exclude [0] (fun u v => edge r92 v u) (a 55) (a 26) 1 t1 c92 (by decide +kernel)
  have t7 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b7
  have b8 : a 56 ≠ 1 := exclude [0] (fun u v => edge r94 v u) (a 56) (a 27) 1 d27 c94 (by decide +kernel)
  have t8 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b8
  have b9 : a 59 ≠ 1 := exclude [0] (fun u v => edge r97 v u) (a 59) (a 29) 1 d29 c97 (by decide +kernel)
  have t9 : a 59 ∈ [0] := remove (a 59) 1 [0,1] d59 b9
  have b10 : a 32 ≠ 1 := exclude [0] (edge r107) (a 32) (a 39) 1 d39 c107 (by decide +kernel)
  have t10 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b10
  have b11 : a 40 ≠ 1 := exclude [0] (fun u v => edge r127 v u) (a 40) (a 39) 1 d39 c127 (by decide +kernel)
  have t11 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b11
  have b12 : a 49 ≠ 1 := exclude [0] (edge r152) (a 49) (a 51) 1 t3 c152 (by decide +kernel)
  have t12 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b12
  have b13 : a 50 ≠ 1 := exclude [0] (edge r154) (a 50) (a 52) 1 t4 c154 (by decide +kernel)
  have t13 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b13
  have b14 : a 57 ≠ 2 := exclude [0] (fun u v => edge r155 v u) (a 57) (a 50) 2 t13 c155 (by decide +kernel)
  have t14 : a 57 ∈ [0] := remove (a 57) 2 [0,2] d57 b14
  have b15 : a 8 ≠ 1 := exclude [0] (edge r36) (a 8) (a 24) 1 t6 c36 (by decide +kernel)
  have t15 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk3 (a : Nat → Nat)
    (d38 : a 38 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d32 : a 32 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (c37 : edge r37 (a 8) (a 38)=true)
    (c57 : edge r57 (a 15) (a 17)=true)
    (c61 : edge r61 (a 16) (a 18)=true)
    (c99 : edge r99 (a 30) (a 32)=true)
    (c104 : edge r104 (a 31) (a 38)=true)
    : a 38 ∈ [0] ∧ a 15 ∈ [0] ∧ a 16 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] := by
  have b0 : a 38 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 38) (a 8) 1 d8 c37 (by decide +kernel)
  have t0 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b0
  have b1 : a 15 ≠ 1 := exclude [0] (edge r57) (a 15) (a 17) 1 d17 c57 (by decide +kernel)
  have t1 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b1
  have b2 : a 16 ≠ 1 := exclude [0] (edge r61) (a 16) (a 18) 1 d18 c61 (by decide +kernel)
  have t2 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b2
  have b3 : a 30 ≠ 1 := exclude [0] (edge r99) (a 30) (a 32) 1 d32 c99 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b3
  have b4 : a 31 ≠ 1 := exclude [0] (edge r104) (a 31) (a 38) 1 t0 c104 (by decide +kernel)
  have t4 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_226
