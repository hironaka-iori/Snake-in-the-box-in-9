import PartitionData205_193
namespace PartitionCover205_193
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1,2])
    (d13 : a 13 ∈ [0,3])
    (d7 : a 7 ∈ [0,1,2,3])
    (d15 : a 15 ∈ [0])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    : a 5 ∈ [0,1] ∧ a 7 ∈ [0,2] := by
  have b0 : a 5 ≠ 2 := exclude [0,3] (edge r21) (a 5) (a 13) 2 d13 c21 (by decide +kernel)
  have t0 : a 5 ∈ [0,1] := remove (a 5) 2 [0,1,2] d5 b0
  have b1 : a 7 ≠ 1 := exclude [0] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t1 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b1
  have b2 : a 7 ≠ 3 := exclude [0] (edge r26) (a 7) (a 15) 3 d15 c26 (by decide +kernel)
  have t2 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] t1 b2
  exact And.intro t0 (t2)

theorem chunk13 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d4 : a 4 ∈ [0,4])
    (d12 : a 12 ∈ [0,6])
    (d20 : a 20 ∈ [0,6])
    (d14 : a 14 ∈ [0,6])
    (d8 : a 8 ∈ [0,3])
    (d10 : a 10 ∈ [0,6])
    (d13 : a 13 ∈ [0,3])
    (d29 : a 29 ∈ [0,6])
    (d30 : a 30 ∈ [0,6])
    (d16 : a 16 ∈ [0,3])
    (d21 : a 21 ∈ [0,3])
    (d25 : a 25 ∈ [0,6])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 3 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 14 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 13 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 16 ∈ [0] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 1 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 2 ≠ 2 := exclude [0] (edge r9) (a 2) (a 3) 2 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b1
  have b2 : a 6 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 1 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b2
  have b3 : a 7 ≠ 2 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 2 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b3
  have b4 : a 4 ≠ 4 := exclude [0] (edge r17) (a 4) (a 6) 4 t2 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 4 [0,4] d4 b4
  have b5 : a 12 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 6 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 6 [0,6] d12 b5
  have b6 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 t4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0] := remove (a 20) 6 [0,6] d20 b6
  have b7 : a 14 ≠ 6 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 6 t2 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 6 [0,6] d14 b7
  have b8 : a 8 ≠ 3 := exclude [0] (edge r30) (a 8) (a 12) 3 t5 c30 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 3 [0,3] d8 b8
  have b9 : a 10 ≠ 6 := exclude [0] (edge r36) (a 10) (a 14) 6 t7 c36 (by decide +kernel)
  have t9 : a 10 ∈ [0] := remove (a 10) 6 [0,6] d10 b9
  have b10 : a 13 ≠ 3 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 3 t5 c40 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 3 [0,3] d13 b10
  have b11 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 t10 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0] := remove (a 29) 6 [0,6] d29 b11
  have b12 : a 30 ≠ 6 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 6 t7 c46 (by decide +kernel)
  have t12 : a 30 ∈ [0] := remove (a 30) 6 [0,6] d30 b12
  have b13 : a 16 ≠ 3 := exclude [0] (edge r50) (a 16) (a 20) 3 t6 c50 (by decide +kernel)
  have t13 : a 16 ∈ [0] := remove (a 16) 3 [0,3] d16 b13
  have b14 : a 21 ≠ 3 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 3 t6 c60 (by decide +kernel)
  have t14 : a 21 ∈ [0] := remove (a 21) 3 [0,3] d21 b14
  have b15 : a 25 ≠ 6 := exclude [0] (edge r72) (a 25) (a 29) 6 t11 c72 (by decide +kernel)
  have t15 : a 25 ∈ [0] := remove (a 25) 6 [0,6] d25 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk14 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,6])
    (d30 : a 30 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d9 : a 9 ∈ [0,3])
    (d8 : a 8 ∈ [0])
    (d17 : a 17 ∈ [0,3])
    (d16 : a 16 ∈ [0])
    (d18 : a 18 ∈ [0,6])
    (d27 : a 27 ∈ [0,3])
    (d25 : a 25 ∈ [0])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 26 ∈ [0] ∧ a 31 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 18 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 26 ≠ 6 := exclude [0] (edge r74) (a 26) (a 30) 6 d30 c74 (by decide +kernel)
  have t0 : a 26 ∈ [0] := remove (a 26) 6 [0,6] d26 b0
  have b1 : a 31 ≠ 1 := exclude [0] (fun u v => edge r79 v u) (a 31) (a 30) 1 d30 c79 (by decide +kernel)
  have t1 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b1
  have b2 : a 5 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 1 d4 c16 (by decide +kernel)
  have t2 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b2
  have b3 : a 9 ≠ 3 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 3 d8 c28 (by decide +kernel)
  have t3 : a 9 ∈ [0] := remove (a 9) 3 [0,3] d9 b3
  have b4 : a 17 ≠ 3 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 3 d16 c48 (by decide +kernel)
  have t4 : a 17 ∈ [0] := remove (a 17) 3 [0,3] d17 b4
  have b5 : a 18 ≠ 6 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 6 d16 c49 (by decide +kernel)
  have t5 : a 18 ∈ [0] := remove (a 18) 6 [0,6] d18 b5
  have b6 : a 27 ≠ 3 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 3 d25 c71 (by decide +kernel)
  have t6 : a 27 ∈ [0] := remove (a 27) 3 [0,3] d27 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))

theorem chunk15 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d4 : a 4 ∈ [0,4])
    (d12 : a 12 ∈ [0,6])
    (d20 : a 20 ∈ [0,6])
    (d14 : a 14 ∈ [0,6])
    (d8 : a 8 ∈ [0,3])
    (d10 : a 10 ∈ [0,6])
    (d13 : a 13 ∈ [0,3])
    (d29 : a 29 ∈ [0,6])
    (d30 : a 30 ∈ [0,6])
    (d16 : a 16 ∈ [0,3])
    (d21 : a 21 ∈ [0,3])
    (d25 : a 25 ∈ [0,6])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 3 ∈ [1] ∧ a 2 ∈ [2] ∧ a 6 ∈ [1] ∧ a 7 ∈ [2] ∧ a 4 ∈ [4] ∧ a 12 ∈ [6] ∧ a 20 ∈ [6] ∧ a 14 ∈ [6] ∧ a 8 ∈ [3] ∧ a 10 ∈ [6] ∧ a 13 ∈ [3] ∧ a 29 ∈ [6] ∧ a 30 ∈ [6] ∧ a 16 ∈ [3] ∧ a 21 ∈ [3] ∧ a 25 ∈ [6] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 2 ≠ 0 := exclude [1] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b1
  have b2 : a 6 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 6) (a 2) 0 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b2
  have b3 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b3
  have b4 : a 4 ≠ 0 := exclude [1] (edge r17) (a 4) (a 6) 0 t2 c17 (by decide +kernel)
  have t4 : a 4 ∈ [4] := remove (a 4) 0 [0,4] d4 b4
  have b5 : a 12 ≠ 0 := exclude [4] (fun u v => edge r18 v u) (a 12) (a 4) 0 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [6] := remove (a 12) 0 [0,6] d12 b5
  have b6 : a 20 ≠ 0 := exclude [4] (fun u v => edge r19 v u) (a 20) (a 4) 0 t4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [6] := remove (a 20) 0 [0,6] d20 b6
  have b7 : a 14 ≠ 0 := exclude [1] (fun u v => edge r24 v u) (a 14) (a 6) 0 t2 c24 (by decide +kernel)
  have t7 : a 14 ∈ [6] := remove (a 14) 0 [0,6] d14 b7
  have b8 : a 8 ≠ 0 := exclude [6] (edge r30) (a 8) (a 12) 0 t5 c30 (by decide +kernel)
  have t8 : a 8 ∈ [3] := remove (a 8) 0 [0,3] d8 b8
  have b9 : a 10 ≠ 0 := exclude [6] (edge r36) (a 10) (a 14) 0 t7 c36 (by decide +kernel)
  have t9 : a 10 ∈ [6] := remove (a 10) 0 [0,6] d10 b9
  have b10 : a 13 ≠ 0 := exclude [6] (fun u v => edge r40 v u) (a 13) (a 12) 0 t5 c40 (by decide +kernel)
  have t10 : a 13 ∈ [3] := remove (a 13) 0 [0,3] d13 b10
  have b11 : a 29 ≠ 0 := exclude [3] (fun u v => edge r44 v u) (a 29) (a 13) 0 t10 c44 (by decide +kernel)
  have t11 : a 29 ∈ [6] := remove (a 29) 0 [0,6] d29 b11
  have b12 : a 30 ≠ 0 := exclude [6] (fun u v => edge r46 v u) (a 30) (a 14) 0 t7 c46 (by decide +kernel)
  have t12 : a 30 ∈ [6] := remove (a 30) 0 [0,6] d30 b12
  have b13 : a 16 ≠ 0 := exclude [6] (edge r50) (a 16) (a 20) 0 t6 c50 (by decide +kernel)
  have t13 : a 16 ∈ [3] := remove (a 16) 0 [0,3] d16 b13
  have b14 : a 21 ≠ 0 := exclude [6] (fun u v => edge r60 v u) (a 21) (a 20) 0 t6 c60 (by decide +kernel)
  have t14 : a 21 ∈ [3] := remove (a 21) 0 [0,3] d21 b14
  have b15 : a 25 ≠ 0 := exclude [6] (edge r72) (a 25) (a 29) 0 t11 c72 (by decide +kernel)
  have t15 : a 25 ∈ [6] := remove (a 25) 0 [0,6] d25 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_193
