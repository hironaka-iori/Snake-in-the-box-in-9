import PartitionData205_177
namespace PartitionCover205_177
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,2,3])
    (d30 : a 30 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0])
    (c68 : edge r68 (a 24) (a 25)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 26 ∈ [0,2] ∧ a 24 ∈ [0,2] := by
  have b0 : a 26 ≠ 3 := exclude [0,2] (edge r74) (a 26) (a 30) 3 d30 c74 (by decide +kernel)
  have t0 : a 26 ∈ [0,2] := remove (a 26) 3 [0,2,3] d26 b0
  have b1 : a 24 ≠ 1 := exclude [0] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t1 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b1
  have b2 : a 24 ≠ 3 := exclude [0] (edge r68) (a 24) (a 25) 3 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t1 b2
  exact And.intro t0 (t2)

theorem chunk5 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d26 : a 26 ∈ [0,2])
    (d23 : a 23 ∈ [0,2])
    (d24 : a 24 ∈ [0,2])
    (d28 : a 28 ∈ [0,3])
    (d27 : a 27 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 26 ∈ [0] ∧ a 23 ∈ [0] ∧ a 24 ∈ [0] ∧ a 28 ∈ [0] ∧ a 27 ∈ [0] ∧ a 29 ∈ [0] := by
  have b0 : a 9 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 1 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b0
  have b1 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b1
  have b2 : a 8 ≠ 2 := exclude [0] (edge r28) (a 8) (a 9) 2 t0 c28 (by decide +kernel)
  have t2 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b2
  have b3 : a 10 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 2 t2 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b3
  have b4 : a 14 ≠ 1 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 1 t3 c36 (by decide +kernel)
  have t4 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b4
  have b5 : a 15 ≠ 1 := exclude [0] (fun u v => edge r45 v u) (a 15) (a 14) 1 t4 c45 (by decide +kernel)
  have t5 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b5
  have b6 : a 30 ≠ 2 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 2 t4 c46 (by decide +kernel)
  have t6 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b6
  have b7 : a 31 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 1 t5 c47 (by decide +kernel)
  have t7 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b7
  have b8 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 17) 1 t1 c48 (by decide +kernel)
  have t8 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b8
  have b9 : a 18 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 1 t8 c49 (by decide +kernel)
  have t9 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b9
  have b10 : a 26 ≠ 2 := exclude [0] (fun u v => edge r57 v u) (a 26) (a 18) 2 t9 c57 (by decide +kernel)
  have t10 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b10
  have b11 : a 23 ≠ 2 := exclude [0] (edge r67) (a 23) (a 31) 2 t7 c67 (by decide +kernel)
  have t11 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b11
  have b12 : a 24 ≠ 2 := exclude [0] (edge r69) (a 24) (a 26) 2 t10 c69 (by decide +kernel)
  have t12 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b12
  have b13 : a 28 ≠ 3 := exclude [0] (fun u v => edge r70 v u) (a 28) (a 24) 3 t12 c70 (by decide +kernel)
  have t13 : a 28 ∈ [0] := remove (a 28) 3 [0,3] d28 b13
  have b14 : a 27 ≠ 1 := exclude [0] (fun u v => edge r73 v u) (a 27) (a 26) 1 t10 c73 (by decide +kernel)
  have t14 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b14
  have b15 : a 29 ≠ 1 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 1 t13 c76 (by decide +kernel)
  have t15 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d6 : a 6 ∈ [0,4])
    (d14 : a 14 ∈ [0])
    (d7 : a 7 ∈ [0,5])
    (d15 : a 15 ∈ [0])
    (d20 : a 20 ∈ [0,8])
    (d28 : a 28 ∈ [0])
    (d3 : a 3 ∈ [0,2])
    (d4 : a 4 ∈ [0,4])
    (d5 : a 5 ∈ [0,4])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    : a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 20 ∈ [0] ∧ a 3 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 2 ≠ 1 := exclude [0] (edge r12) (a 2) (a 18) 1 d18 c12 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 6 ≠ 4 := exclude [0] (edge r24) (a 6) (a 14) 4 d14 c24 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b1
  have b2 : a 7 ≠ 5 := exclude [0] (edge r26) (a 7) (a 15) 5 d15 c26 (by decide +kernel)
  have t2 : a 7 ∈ [0] := remove (a 7) 5 [0,5] d7 b2
  have b3 : a 20 ≠ 8 := exclude [0] (edge r62) (a 20) (a 28) 8 d28 c62 (by decide +kernel)
  have t3 : a 20 ∈ [0] := remove (a 20) 8 [0,8] d20 b3
  have b4 : a 3 ≠ 2 := exclude [0] (edge r13) (a 3) (a 7) 2 t2 c13 (by decide +kernel)
  have t4 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b4
  have b5 : a 4 ≠ 4 := exclude [0] (edge r17) (a 4) (a 6) 4 t1 c17 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 4 [0,4] d4 b5
  have b6 : a 5 ≠ 4 := exclude [0] (edge r20) (a 5) (a 7) 4 t2 c20 (by decide +kernel)
  have t6 : a 5 ∈ [0] := remove (a 5) 4 [0,4] d5 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))

theorem chunk7 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d26 : a 26 ∈ [0,2])
    (d23 : a 23 ∈ [0,2])
    (d24 : a 24 ∈ [0,2])
    (d28 : a 28 ∈ [0,3])
    (d27 : a 27 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c57 : edge r57 (a 18) (a 26)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 9 ∈ [1] ∧ a 17 ∈ [1] ∧ a 8 ∈ [2] ∧ a 10 ∈ [2] ∧ a 14 ∈ [1] ∧ a 15 ∈ [1] ∧ a 30 ∈ [2] ∧ a 31 ∈ [1] ∧ a 16 ∈ [1] ∧ a 18 ∈ [1] ∧ a 26 ∈ [2] ∧ a 23 ∈ [2] ∧ a 24 ∈ [2] ∧ a 28 ∈ [3] ∧ a 27 ∈ [1] ∧ a 29 ∈ [1] := by
  have b0 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b0
  have b1 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 8 ≠ 0 := exclude [1] (edge r28) (a 8) (a 9) 0 t0 c28 (by decide +kernel)
  have t2 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b2
  have b3 : a 10 ≠ 0 := exclude [2] (fun u v => edge r29 v u) (a 10) (a 8) 0 t2 c29 (by decide +kernel)
  have t3 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b3
  have b4 : a 14 ≠ 0 := exclude [2] (fun u v => edge r36 v u) (a 14) (a 10) 0 t3 c36 (by decide +kernel)
  have t4 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b4
  have b5 : a 15 ≠ 0 := exclude [1] (fun u v => edge r45 v u) (a 15) (a 14) 0 t4 c45 (by decide +kernel)
  have t5 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b5
  have b6 : a 30 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 30) (a 14) 0 t4 c46 (by decide +kernel)
  have t6 : a 30 ∈ [2] := remove (a 30) 0 [0,2] d30 b6
  have b7 : a 31 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 31) (a 15) 0 t5 c47 (by decide +kernel)
  have t7 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b7
  have b8 : a 16 ≠ 0 := exclude [1] (edge r48) (a 16) (a 17) 0 t1 c48 (by decide +kernel)
  have t8 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b8
  have b9 : a 18 ≠ 0 := exclude [1] (fun u v => edge r49 v u) (a 18) (a 16) 0 t8 c49 (by decide +kernel)
  have t9 : a 18 ∈ [1] := remove (a 18) 0 [0,1] d18 b9
  have b10 : a 26 ≠ 0 := exclude [1] (fun u v => edge r57 v u) (a 26) (a 18) 0 t9 c57 (by decide +kernel)
  have t10 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b10
  have b11 : a 23 ≠ 0 := exclude [1] (edge r67) (a 23) (a 31) 0 t7 c67 (by decide +kernel)
  have t11 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b11
  have b12 : a 24 ≠ 0 := exclude [2] (edge r69) (a 24) (a 26) 0 t10 c69 (by decide +kernel)
  have t12 : a 24 ∈ [2] := remove (a 24) 0 [0,2] d24 b12
  have b13 : a 28 ≠ 0 := exclude [2] (fun u v => edge r70 v u) (a 28) (a 24) 0 t12 c70 (by decide +kernel)
  have t13 : a 28 ∈ [3] := remove (a 28) 0 [0,3] d28 b13
  have b14 : a 27 ≠ 0 := exclude [2] (fun u v => edge r73 v u) (a 27) (a 26) 0 t10 c73 (by decide +kernel)
  have t14 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b14
  have b15 : a 29 ≠ 0 := exclude [3] (fun u v => edge r76 v u) (a 29) (a 28) 0 t13 c76 (by decide +kernel)
  have t15 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_177
