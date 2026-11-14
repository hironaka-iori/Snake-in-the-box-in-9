import PartitionData205_171
namespace PartitionCover205_171
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,3])
    (d1 : a 1 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d8 : a 8 ∈ [0,4])
    (d10 : a 10 ∈ [0,4])
    (d12 : a 12 ∈ [0,1])
    (d11 : a 11 ∈ [0,6])
    (d14 : a 14 ∈ [0,2])
    (d26 : a 26 ∈ [0,2])
    (d15 : a 15 ∈ [0,3])
    (d27 : a 27 ∈ [0,1])
    (d28 : a 28 ∈ [0,4])
    (d30 : a 30 ∈ [0,4])
    (d31 : a 31 ∈ [0,6])
    (d16 : a 16 ∈ [0,2])
    (d18 : a 18 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 12 ∈ [0] ∧ a 11 ∈ [0] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0] := by
  have b0 : a 9 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 3 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [0] := remove (a 9) 3 [0,3] d9 b0
  have b1 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b1
  have b2 : a 8 ≠ 4 := exclude [0] (edge r28) (a 8) (a 9) 4 t0 c28 (by decide +kernel)
  have t2 : a 8 ∈ [0] := remove (a 8) 4 [0,4] d8 b2
  have b3 : a 10 ≠ 4 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 4 t2 c29 (by decide +kernel)
  have t3 : a 10 ∈ [0] := remove (a 10) 4 [0,4] d10 b3
  have b4 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 t2 c30 (by decide +kernel)
  have t4 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b4
  have b5 : a 11 ≠ 6 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 6 t0 c32 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b5
  have b6 : a 14 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 2 t3 c36 (by decide +kernel)
  have t6 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b6
  have b7 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 2 t3 c37 (by decide +kernel)
  have t7 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b7
  have b8 : a 15 ≠ 3 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 3 t5 c38 (by decide +kernel)
  have t8 : a 15 ∈ [0] := remove (a 15) 3 [0,3] d15 b8
  have b9 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 t5 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b9
  have b10 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 t4 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 4 [0,4] d28 b10
  have b11 : a 30 ≠ 4 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 4 t6 c46 (by decide +kernel)
  have t11 : a 30 ∈ [0] := remove (a 30) 4 [0,4] d30 b11
  have b12 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 t8 c47 (by decide +kernel)
  have t12 : a 31 ∈ [0] := remove (a 31) 6 [0,6] d31 b12
  have b13 : a 16 ≠ 2 := exclude [0] (edge r48) (a 16) (a 17) 2 t1 c48 (by decide +kernel)
  have t13 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b13
  have b14 : a 18 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 1 t13 c49 (by decide +kernel)
  have t14 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b14
  have b15 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 1 t1 c52 (by decide +kernel)
  have t15 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,5])
    (d19 : a 19 ∈ [0])
    (d29 : a 29 ∈ [0,4])
    (d28 : a 28 ∈ [0])
    (d2 : a 2 ∈ [0,2])
    (d18 : a 18 ∈ [0])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d7 : a 7 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d5 : a 5 ∈ [0,4])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 23 ∈ [0] ∧ a 29 ∈ [0] ∧ a 2 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 23 ≠ 5 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 5 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [0] := remove (a 23) 5 [0,5] d23 b0
  have b1 : a 29 ≠ 4 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 4 d28 c76 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 4 [0,4] d29 b1
  have b2 : a 2 ≠ 2 := exclude [0] (edge r12) (a 2) (a 18) 2 d18 c12 (by decide +kernel)
  have t2 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b2
  have b3 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b3
  have b4 : a 6 ≠ 2 := exclude [0] (edge r24) (a 6) (a 14) 2 d14 c24 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b4
  have b5 : a 7 ≠ 1 := exclude [0] (edge r26) (a 7) (a 15) 1 d15 c26 (by decide +kernel)
  have t5 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b5
  have b6 : a 5 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 4 t3 c16 (by decide +kernel)
  have t6 : a 5 ∈ [0] := remove (a 5) 4 [0,4] d5 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))

theorem chunk10 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,3])
    (d1 : a 1 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d8 : a 8 ∈ [0,4])
    (d10 : a 10 ∈ [0,4])
    (d12 : a 12 ∈ [0,1])
    (d11 : a 11 ∈ [0,6])
    (d14 : a 14 ∈ [0,2])
    (d26 : a 26 ∈ [0,2])
    (d15 : a 15 ∈ [0,3])
    (d27 : a 27 ∈ [0,1])
    (d28 : a 28 ∈ [0,4])
    (d30 : a 30 ∈ [0,4])
    (d31 : a 31 ∈ [0,6])
    (d16 : a 16 ∈ [0,2])
    (d18 : a 18 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 9 ∈ [3] ∧ a 17 ∈ [1] ∧ a 8 ∈ [4] ∧ a 10 ∈ [4] ∧ a 12 ∈ [1] ∧ a 11 ∈ [6] ∧ a 14 ∈ [2] ∧ a 26 ∈ [2] ∧ a 15 ∈ [3] ∧ a 27 ∈ [1] ∧ a 28 ∈ [4] ∧ a 30 ∈ [4] ∧ a 31 ∈ [6] ∧ a 16 ∈ [2] ∧ a 18 ∈ [1] ∧ a 19 ∈ [1] := by
  have b0 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [3] := remove (a 9) 0 [0,3] d9 b0
  have b1 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 8 ≠ 0 := exclude [3] (edge r28) (a 8) (a 9) 0 t0 c28 (by decide +kernel)
  have t2 : a 8 ∈ [4] := remove (a 8) 0 [0,4] d8 b2
  have b3 : a 10 ≠ 0 := exclude [4] (fun u v => edge r29 v u) (a 10) (a 8) 0 t2 c29 (by decide +kernel)
  have t3 : a 10 ∈ [4] := remove (a 10) 0 [0,4] d10 b3
  have b4 : a 12 ≠ 0 := exclude [4] (fun u v => edge r30 v u) (a 12) (a 8) 0 t2 c30 (by decide +kernel)
  have t4 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b4
  have b5 : a 11 ≠ 0 := exclude [3] (fun u v => edge r32 v u) (a 11) (a 9) 0 t0 c32 (by decide +kernel)
  have t5 : a 11 ∈ [6] := remove (a 11) 0 [0,6] d11 b5
  have b6 : a 14 ≠ 0 := exclude [4] (fun u v => edge r36 v u) (a 14) (a 10) 0 t3 c36 (by decide +kernel)
  have t6 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b6
  have b7 : a 26 ≠ 0 := exclude [4] (fun u v => edge r37 v u) (a 26) (a 10) 0 t3 c37 (by decide +kernel)
  have t7 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b7
  have b8 : a 15 ≠ 0 := exclude [6] (fun u v => edge r38 v u) (a 15) (a 11) 0 t5 c38 (by decide +kernel)
  have t8 : a 15 ∈ [3] := remove (a 15) 0 [0,3] d15 b8
  have b9 : a 27 ≠ 0 := exclude [6] (fun u v => edge r39 v u) (a 27) (a 11) 0 t5 c39 (by decide +kernel)
  have t9 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b9
  have b10 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 t4 c42 (by decide +kernel)
  have t10 : a 28 ∈ [4] := remove (a 28) 0 [0,4] d28 b10
  have b11 : a 30 ≠ 0 := exclude [2] (fun u v => edge r46 v u) (a 30) (a 14) 0 t6 c46 (by decide +kernel)
  have t11 : a 30 ∈ [4] := remove (a 30) 0 [0,4] d30 b11
  have b12 : a 31 ≠ 0 := exclude [3] (fun u v => edge r47 v u) (a 31) (a 15) 0 t8 c47 (by decide +kernel)
  have t12 : a 31 ∈ [6] := remove (a 31) 0 [0,6] d31 b12
  have b13 : a 16 ≠ 0 := exclude [1] (edge r48) (a 16) (a 17) 0 t1 c48 (by decide +kernel)
  have t13 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b13
  have b14 : a 18 ≠ 0 := exclude [2] (fun u v => edge r49 v u) (a 18) (a 16) 0 t13 c49 (by decide +kernel)
  have t14 : a 18 ∈ [1] := remove (a 18) 0 [0,1] d18 b14
  have b15 : a 19 ≠ 0 := exclude [1] (fun u v => edge r52 v u) (a 19) (a 17) 0 t1 c52 (by decide +kernel)
  have t15 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk11 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,5])
    (d19 : a 19 ∈ [1])
    (d29 : a 29 ∈ [0,4])
    (d28 : a 28 ∈ [4])
    (d2 : a 2 ∈ [0,2])
    (d18 : a 18 ∈ [1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [1])
    (d6 : a 6 ∈ [0,2])
    (d14 : a 14 ∈ [2])
    (d7 : a 7 ∈ [0,1])
    (d15 : a 15 ∈ [3])
    (d5 : a 5 ∈ [0,4])
    (c12 : edge r12 (a 2) (a 18)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 23 ∈ [5] ∧ a 29 ∈ [4] ∧ a 2 ∈ [2] ∧ a 4 ∈ [1] ∧ a 6 ∈ [2] ∧ a 7 ∈ [1] ∧ a 5 ∈ [4] := by
  have b0 : a 23 ≠ 0 := exclude [1] (fun u v => edge r58 v u) (a 23) (a 19) 0 d19 c58 (by decide +kernel)
  have t0 : a 23 ∈ [5] := remove (a 23) 0 [0,5] d23 b0
  have b1 : a 29 ≠ 0 := exclude [4] (fun u v => edge r76 v u) (a 29) (a 28) 0 d28 c76 (by decide +kernel)
  have t1 : a 29 ∈ [4] := remove (a 29) 0 [0,4] d29 b1
  have b2 : a 2 ≠ 0 := exclude [1] (edge r12) (a 2) (a 18) 0 d18 c12 (by decide +kernel)
  have t2 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b2
  have b3 : a 4 ≠ 0 := exclude [1] (edge r18) (a 4) (a 12) 0 d12 c18 (by decide +kernel)
  have t3 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b3
  have b4 : a 6 ≠ 0 := exclude [2] (edge r24) (a 6) (a 14) 0 d14 c24 (by decide +kernel)
  have t4 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b4
  have b5 : a 7 ≠ 0 := exclude [3] (edge r26) (a 7) (a 15) 0 d15 c26 (by decide +kernel)
  have t5 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b5
  have b6 : a 5 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 5) (a 4) 0 t3 c16 (by decide +kernel)
  have t6 : a 5 ∈ [4] := remove (a 5) 0 [0,4] d5 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_171
