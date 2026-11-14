import PartitionData205_208
namespace PartitionCover205_208
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [0])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,2])
    (d7 : a 7 ∈ [0,4])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,6])
    (d20 : a 20 ∈ [0,6])
    (d5 : a 5 ∈ [0,3])
    (d21 : a 21 ∈ [0,6])
    (d15 : a 15 ∈ [0,8])
    (d8 : a 8 ∈ [0,6])
    (d11 : a 11 ∈ [0,8])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,12])
    (d31 : a 31 ∈ [0,6])
    (d16 : a 16 ∈ [0,3])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    : a 3 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 5 ∈ [0] ∧ a 21 ∈ [0] ∧ a 15 ∈ [0] ∧ a 8 ∈ [0] ∧ a 11 ∈ [0] ∧ a 13 ∈ [0] ∧ a 29 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 3 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 2 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b0
  have b1 : a 2 ≠ 2 := exclude [0] (edge r9) (a 2) (a 3) 2 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b1
  have b2 : a 6 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 2 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b2
  have b3 : a 7 ≠ 4 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 4 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 4 [0,4] d7 b3
  have b4 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t2 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b4
  have b5 : a 12 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 6 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 6 [0,6] d12 b5
  have b6 : a 20 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 6 t4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0] := remove (a 20) 6 [0,6] d20 b6
  have b7 : a 5 ≠ 3 := exclude [0] (edge r20) (a 5) (a 7) 3 t3 c20 (by decide +kernel)
  have t7 : a 5 ∈ [0] := remove (a 5) 3 [0,3] d5 b7
  have b8 : a 21 ≠ 6 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 6 t7 c22 (by decide +kernel)
  have t8 : a 21 ∈ [0] := remove (a 21) 6 [0,6] d21 b8
  have b9 : a 15 ≠ 8 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 8 t3 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 8 [0,8] d15 b9
  have b10 : a 8 ≠ 6 := exclude [0] (edge r30) (a 8) (a 12) 6 t5 c30 (by decide +kernel)
  have t10 : a 8 ∈ [0] := remove (a 8) 6 [0,6] d8 b10
  have b11 : a 11 ≠ 8 := exclude [0] (edge r38) (a 11) (a 15) 8 t9 c38 (by decide +kernel)
  have t11 : a 11 ∈ [0] := remove (a 11) 8 [0,8] d11 b11
  have b12 : a 13 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 1 t5 c40 (by decide +kernel)
  have t12 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b12
  have b13 : a 29 ≠ 12 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 12 t12 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0] := remove (a 29) 12 [0,12] d29 b13
  have b14 : a 31 ≠ 6 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 6 t9 c47 (by decide +kernel)
  have t14 : a 31 ∈ [0] := remove (a 31) 6 [0,6] d31 b14
  have b15 : a 16 ≠ 3 := exclude [0] (edge r50) (a 16) (a 20) 3 t6 c50 (by decide +kernel)
  have t15 : a 16 ∈ [0] := remove (a 16) 3 [0,3] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk17 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,3])
    (d21 : a 21 ∈ [0])
    (d25 : a 25 ∈ [0,12])
    (d29 : a 29 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d9 : a 9 ∈ [0,8])
    (d8 : a 8 ∈ [0])
    (d19 : a 19 ∈ [0,3])
    (d27 : a 27 ∈ [0,12])
    (d26 : a 26 ∈ [0,9])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 17 ∈ [0] ∧ a 25 ∈ [0] ∧ a 30 ∈ [0] ∧ a 9 ∈ [0] ∧ a 19 ∈ [0] ∧ a 27 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 17 ≠ 3 := exclude [0] (edge r53) (a 17) (a 21) 3 d21 c53 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 3 [0,3] d17 b0
  have b1 : a 25 ≠ 12 := exclude [0] (edge r72) (a 25) (a 29) 12 d29 c72 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 12 [0,12] d25 b1
  have b2 : a 30 ≠ 1 := exclude [0] (edge r79) (a 30) (a 31) 1 d31 c79 (by decide +kernel)
  have t2 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b2
  have b3 : a 9 ≠ 8 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 8 d8 c28 (by decide +kernel)
  have t3 : a 9 ∈ [0] := remove (a 9) 8 [0,8] d9 b3
  have b4 : a 19 ≠ 3 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 3 t0 c52 (by decide +kernel)
  have t4 : a 19 ∈ [0] := remove (a 19) 3 [0,3] d19 b4
  have b5 : a 27 ≠ 12 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 12 t1 c71 (by decide +kernel)
  have t5 : a 27 ∈ [0] := remove (a 27) 12 [0,12] d27 b5
  have b6 : a 26 ≠ 9 := exclude [0] (edge r73) (a 26) (a 27) 9 t5 c73 (by decide +kernel)
  have t6 : a 26 ∈ [0] := remove (a 26) 9 [0,9] d26 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))

theorem chunk18 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,2])
    (d7 : a 7 ∈ [0,4])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,6])
    (d20 : a 20 ∈ [0,6])
    (d5 : a 5 ∈ [0,3])
    (d21 : a 21 ∈ [0,6])
    (d15 : a 15 ∈ [0,8])
    (d8 : a 8 ∈ [0,6])
    (d11 : a 11 ∈ [0,8])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,12])
    (d31 : a 31 ∈ [0,6])
    (d16 : a 16 ∈ [0,3])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    : a 3 ∈ [2] ∧ a 2 ∈ [2] ∧ a 6 ∈ [2] ∧ a 7 ∈ [4] ∧ a 4 ∈ [1] ∧ a 12 ∈ [6] ∧ a 20 ∈ [6] ∧ a 5 ∈ [3] ∧ a 21 ∈ [6] ∧ a 15 ∈ [8] ∧ a 8 ∈ [6] ∧ a 11 ∈ [8] ∧ a 13 ∈ [1] ∧ a 29 ∈ [12] ∧ a 31 ∈ [6] ∧ a 16 ∈ [3] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b0
  have b1 : a 2 ≠ 0 := exclude [2] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b1
  have b2 : a 6 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 6) (a 2) 0 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b2
  have b3 : a 7 ≠ 0 := exclude [2] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [4] := remove (a 7) 0 [0,4] d7 b3
  have b4 : a 4 ≠ 0 := exclude [2] (edge r17) (a 4) (a 6) 0 t2 c17 (by decide +kernel)
  have t4 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b4
  have b5 : a 12 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 12) (a 4) 0 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [6] := remove (a 12) 0 [0,6] d12 b5
  have b6 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [6] := remove (a 20) 0 [0,6] d20 b6
  have b7 : a 5 ≠ 0 := exclude [4] (edge r20) (a 5) (a 7) 0 t3 c20 (by decide +kernel)
  have t7 : a 5 ∈ [3] := remove (a 5) 0 [0,3] d5 b7
  have b8 : a 21 ≠ 0 := exclude [3] (fun u v => edge r22 v u) (a 21) (a 5) 0 t7 c22 (by decide +kernel)
  have t8 : a 21 ∈ [6] := remove (a 21) 0 [0,6] d21 b8
  have b9 : a 15 ≠ 0 := exclude [4] (fun u v => edge r26 v u) (a 15) (a 7) 0 t3 c26 (by decide +kernel)
  have t9 : a 15 ∈ [8] := remove (a 15) 0 [0,8] d15 b9
  have b10 : a 8 ≠ 0 := exclude [6] (edge r30) (a 8) (a 12) 0 t5 c30 (by decide +kernel)
  have t10 : a 8 ∈ [6] := remove (a 8) 0 [0,6] d8 b10
  have b11 : a 11 ≠ 0 := exclude [8] (edge r38) (a 11) (a 15) 0 t9 c38 (by decide +kernel)
  have t11 : a 11 ∈ [8] := remove (a 11) 0 [0,8] d11 b11
  have b12 : a 13 ≠ 0 := exclude [6] (fun u v => edge r40 v u) (a 13) (a 12) 0 t5 c40 (by decide +kernel)
  have t12 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b12
  have b13 : a 29 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 29) (a 13) 0 t12 c44 (by decide +kernel)
  have t13 : a 29 ∈ [12] := remove (a 29) 0 [0,12] d29 b13
  have b14 : a 31 ≠ 0 := exclude [8] (fun u v => edge r47 v u) (a 31) (a 15) 0 t9 c47 (by decide +kernel)
  have t14 : a 31 ∈ [6] := remove (a 31) 0 [0,6] d31 b14
  have b15 : a 16 ≠ 0 := exclude [6] (edge r50) (a 16) (a 20) 0 t6 c50 (by decide +kernel)
  have t15 : a 16 ∈ [3] := remove (a 16) 0 [0,3] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk19 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,3])
    (d21 : a 21 ∈ [6])
    (d25 : a 25 ∈ [0,12])
    (d29 : a 29 ∈ [12])
    (d30 : a 30 ∈ [0,1])
    (d31 : a 31 ∈ [6])
    (d9 : a 9 ∈ [0,8])
    (d8 : a 8 ∈ [6])
    (d19 : a 19 ∈ [0,3])
    (d27 : a 27 ∈ [0,12])
    (d26 : a 26 ∈ [0,9])
    (c28 : edge r28 (a 8) (a 9)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c79 : edge r79 (a 30) (a 31)=true)
    : a 17 ∈ [3] ∧ a 25 ∈ [12] ∧ a 30 ∈ [1] ∧ a 9 ∈ [8] ∧ a 19 ∈ [3] ∧ a 27 ∈ [12] ∧ a 26 ∈ [9] := by
  have b0 : a 17 ≠ 0 := exclude [6] (edge r53) (a 17) (a 21) 0 d21 c53 (by decide +kernel)
  have t0 : a 17 ∈ [3] := remove (a 17) 0 [0,3] d17 b0
  have b1 : a 25 ≠ 0 := exclude [12] (edge r72) (a 25) (a 29) 0 d29 c72 (by decide +kernel)
  have t1 : a 25 ∈ [12] := remove (a 25) 0 [0,12] d25 b1
  have b2 : a 30 ≠ 0 := exclude [6] (edge r79) (a 30) (a 31) 0 d31 c79 (by decide +kernel)
  have t2 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b2
  have b3 : a 9 ≠ 0 := exclude [6] (fun u v => edge r28 v u) (a 9) (a 8) 0 d8 c28 (by decide +kernel)
  have t3 : a 9 ∈ [8] := remove (a 9) 0 [0,8] d9 b3
  have b4 : a 19 ≠ 0 := exclude [3] (fun u v => edge r52 v u) (a 19) (a 17) 0 t0 c52 (by decide +kernel)
  have t4 : a 19 ∈ [3] := remove (a 19) 0 [0,3] d19 b4
  have b5 : a 27 ≠ 0 := exclude [12] (fun u v => edge r71 v u) (a 27) (a 25) 0 t1 c71 (by decide +kernel)
  have t5 : a 27 ∈ [12] := remove (a 27) 0 [0,12] d27 b5
  have b6 : a 26 ≠ 0 := exclude [12] (edge r73) (a 26) (a 27) 0 t5 c73 (by decide +kernel)
  have t6 : a 26 ∈ [9] := remove (a 26) 0 [0,9] d26 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_208
