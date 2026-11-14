import PartitionData205_183
namespace PartitionCover205_183
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0,3])
    (d12 : a 12 ∈ [0,1])
    (d19 : a 19 ∈ [0,6])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d13 : a 13 ∈ [0,12])
    (d24 : a 24 ∈ [0,6])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,2])
    (d15 : a 15 ∈ [0,3])
    (d16 : a 16 ∈ [0,6])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 19)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c28 : edge r28 (a 8) (a 10)=true)
    (c31 : edge r31 (a 9) (a 11)=true)
    (c32 : edge r32 (a 9) (a 13)=true)
    (c33 : edge r33 (a 9) (a 24)=true)
    (c36 : edge r36 (a 10) (a 25)=true)
    (c37 : edge r37 (a 11) (a 26)=true)
    (c45 : edge r45 (a 15) (a 19)=true)
    (c49 : edge r49 (a 16) (a 24)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 19 ∈ [0] ∧ a 14 ∈ [0] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b1
  have b2 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b2
  have b3 : a 11 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 1 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b3
  have b4 : a 4 ≠ 3 := exclude [0] (edge r17) (a 4) (a 6) 3 t1 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 3 [0,3] d4 b4
  have b5 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b5
  have b6 : a 19 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 19) (a 4) 6 t4 c19 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 6 [0,6] d19 b6
  have b7 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 t1 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b7
  have b8 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 10) 1 t2 c28 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b8
  have b9 : a 9 ≠ 1 := exclude [0] (edge r31) (a 9) (a 11) 1 t3 c31 (by decide +kernel)
  have t9 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b9
  have b10 : a 13 ≠ 12 := exclude [0] (fun u v => edge r32 v u) (a 13) (a 9) 12 t9 c32 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 12 [0,12] d13 b10
  have b11 : a 24 ≠ 6 := exclude [0] (fun u v => edge r33 v u) (a 24) (a 9) 6 t9 c33 (by decide +kernel)
  have t11 : a 24 ∈ [0] := remove (a 24) 6 [0,6] d24 b11
  have b12 : a 25 ≠ 3 := exclude [0] (fun u v => edge r36 v u) (a 25) (a 10) 3 t2 c36 (by decide +kernel)
  have t12 : a 25 ∈ [0] := remove (a 25) 3 [0,3] d25 b12
  have b13 : a 26 ≠ 2 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 11) 2 t3 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b13
  have b14 : a 15 ≠ 3 := exclude [0] (edge r45) (a 15) (a 19) 3 t6 c45 (by decide +kernel)
  have t14 : a 15 ∈ [0] := remove (a 15) 3 [0,3] d15 b14
  have b15 : a 16 ≠ 6 := exclude [0] (edge r49) (a 16) (a 24) 6 t11 c49 (by decide +kernel)
  have t15 : a 16 ∈ [0] := remove (a 16) 6 [0,6] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk17 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2])
    (d26 : a 26 ∈ [0])
    (d27 : a 27 ∈ [0,6])
    (d19 : a 19 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d30 : a 30 ∈ [0,2])
    (d5 : a 5 ∈ [0,3])
    (d4 : a 4 ∈ [0])
    (d22 : a 22 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c53 : edge r53 (a 18) (a 22)=true)
    (c54 : edge r54 (a 18) (a 26)=true)
    (c57 : edge r57 (a 19) (a 27)=true)
    (c60 : edge r60 (a 21) (a 22)=true)
    (c69 : edge r69 (a 25) (a 29)=true)
    (c70 : edge r70 (a 26) (a 30)=true)
    : a 18 ∈ [0] ∧ a 27 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 5 ∈ [0] ∧ a 22 ∈ [0] ∧ a 21 ∈ [0] := by
  have b0 : a 18 ≠ 2 := exclude [0] (edge r54) (a 18) (a 26) 2 d26 c54 (by decide +kernel)
  have t0 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b0
  have b1 : a 27 ≠ 6 := exclude [0] (fun u v => edge r57 v u) (a 27) (a 19) 6 d19 c57 (by decide +kernel)
  have t1 : a 27 ∈ [0] := remove (a 27) 6 [0,6] d27 b1
  have b2 : a 29 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 29) (a 25) 1 d25 c69 (by decide +kernel)
  have t2 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b2
  have b3 : a 30 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 30) (a 26) 2 d26 c70 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b3
  have b4 : a 5 ≠ 3 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 3 d4 c16 (by decide +kernel)
  have t4 : a 5 ∈ [0] := remove (a 5) 3 [0,3] d5 b4
  have b5 : a 22 ≠ 2 := exclude [0] (fun u v => edge r53 v u) (a 22) (a 18) 2 t0 c53 (by decide +kernel)
  have t5 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b5
  have b6 : a 21 ≠ 1 := exclude [0] (edge r60) (a 21) (a 22) 1 t5 c60 (by decide +kernel)
  have t6 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))

theorem chunk18 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0,3])
    (d12 : a 12 ∈ [0,1])
    (d19 : a 19 ∈ [0,6])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0,1])
    (d13 : a 13 ∈ [0,12])
    (d24 : a 24 ∈ [0,6])
    (d25 : a 25 ∈ [0,3])
    (d26 : a 26 ∈ [0,2])
    (d15 : a 15 ∈ [0,3])
    (d16 : a 16 ∈ [0,6])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 19)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c28 : edge r28 (a 8) (a 10)=true)
    (c31 : edge r31 (a 9) (a 11)=true)
    (c32 : edge r32 (a 9) (a 13)=true)
    (c33 : edge r33 (a 9) (a 24)=true)
    (c36 : edge r36 (a 10) (a 25)=true)
    (c37 : edge r37 (a 11) (a 26)=true)
    (c45 : edge r45 (a 15) (a 19)=true)
    (c49 : edge r49 (a 16) (a 24)=true)
    : a 3 ∈ [1] ∧ a 6 ∈ [2] ∧ a 10 ∈ [1] ∧ a 11 ∈ [1] ∧ a 4 ∈ [3] ∧ a 12 ∈ [1] ∧ a 19 ∈ [6] ∧ a 14 ∈ [2] ∧ a 8 ∈ [1] ∧ a 9 ∈ [1] ∧ a 13 ∈ [12] ∧ a 24 ∈ [6] ∧ a 25 ∈ [3] ∧ a 26 ∈ [2] ∧ a 15 ∈ [3] ∧ a 16 ∈ [6] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 6 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 6) (a 2) 0 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b1
  have b2 : a 10 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 10) (a 2) 0 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b2
  have b3 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b3
  have b4 : a 4 ≠ 0 := exclude [2] (edge r17) (a 4) (a 6) 0 t1 c17 (by decide +kernel)
  have t4 : a 4 ∈ [3] := remove (a 4) 0 [0,3] d4 b4
  have b5 : a 12 ≠ 0 := exclude [3] (fun u v => edge r18 v u) (a 12) (a 4) 0 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b5
  have b6 : a 19 ≠ 0 := exclude [3] (fun u v => edge r19 v u) (a 19) (a 4) 0 t4 c19 (by decide +kernel)
  have t6 : a 19 ∈ [6] := remove (a 19) 0 [0,6] d19 b6
  have b7 : a 14 ≠ 0 := exclude [2] (fun u v => edge r24 v u) (a 14) (a 6) 0 t1 c24 (by decide +kernel)
  have t7 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b7
  have b8 : a 8 ≠ 0 := exclude [1] (edge r28) (a 8) (a 10) 0 t2 c28 (by decide +kernel)
  have t8 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b8
  have b9 : a 9 ≠ 0 := exclude [1] (edge r31) (a 9) (a 11) 0 t3 c31 (by decide +kernel)
  have t9 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b9
  have b10 : a 13 ≠ 0 := exclude [1] (fun u v => edge r32 v u) (a 13) (a 9) 0 t9 c32 (by decide +kernel)
  have t10 : a 13 ∈ [12] := remove (a 13) 0 [0,12] d13 b10
  have b11 : a 24 ≠ 0 := exclude [1] (fun u v => edge r33 v u) (a 24) (a 9) 0 t9 c33 (by decide +kernel)
  have t11 : a 24 ∈ [6] := remove (a 24) 0 [0,6] d24 b11
  have b12 : a 25 ≠ 0 := exclude [1] (fun u v => edge r36 v u) (a 25) (a 10) 0 t2 c36 (by decide +kernel)
  have t12 : a 25 ∈ [3] := remove (a 25) 0 [0,3] d25 b12
  have b13 : a 26 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 26) (a 11) 0 t3 c37 (by decide +kernel)
  have t13 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b13
  have b14 : a 15 ≠ 0 := exclude [6] (edge r45) (a 15) (a 19) 0 t6 c45 (by decide +kernel)
  have t14 : a 15 ∈ [3] := remove (a 15) 0 [0,3] d15 b14
  have b15 : a 16 ≠ 0 := exclude [6] (edge r49) (a 16) (a 24) 0 t11 c49 (by decide +kernel)
  have t15 : a 16 ∈ [6] := remove (a 16) 0 [0,6] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk19 (a : Nat → Nat)
    (d18 : a 18 ∈ [0,2])
    (d26 : a 26 ∈ [2])
    (d27 : a 27 ∈ [0,6])
    (d19 : a 19 ∈ [6])
    (d29 : a 29 ∈ [0,1])
    (d25 : a 25 ∈ [3])
    (d30 : a 30 ∈ [0,2])
    (d5 : a 5 ∈ [0,3])
    (d4 : a 4 ∈ [3])
    (d22 : a 22 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c53 : edge r53 (a 18) (a 22)=true)
    (c54 : edge r54 (a 18) (a 26)=true)
    (c57 : edge r57 (a 19) (a 27)=true)
    (c60 : edge r60 (a 21) (a 22)=true)
    (c69 : edge r69 (a 25) (a 29)=true)
    (c70 : edge r70 (a 26) (a 30)=true)
    : a 18 ∈ [2] ∧ a 27 ∈ [6] ∧ a 29 ∈ [1] ∧ a 30 ∈ [2] ∧ a 5 ∈ [3] ∧ a 22 ∈ [2] ∧ a 21 ∈ [1] := by
  have b0 : a 18 ≠ 0 := exclude [2] (edge r54) (a 18) (a 26) 0 d26 c54 (by decide +kernel)
  have t0 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b0
  have b1 : a 27 ≠ 0 := exclude [6] (fun u v => edge r57 v u) (a 27) (a 19) 0 d19 c57 (by decide +kernel)
  have t1 : a 27 ∈ [6] := remove (a 27) 0 [0,6] d27 b1
  have b2 : a 29 ≠ 0 := exclude [3] (fun u v => edge r69 v u) (a 29) (a 25) 0 d25 c69 (by decide +kernel)
  have t2 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b2
  have b3 : a 30 ≠ 0 := exclude [2] (fun u v => edge r70 v u) (a 30) (a 26) 0 d26 c70 (by decide +kernel)
  have t3 : a 30 ∈ [2] := remove (a 30) 0 [0,2] d30 b3
  have b4 : a 5 ≠ 0 := exclude [3] (fun u v => edge r16 v u) (a 5) (a 4) 0 d4 c16 (by decide +kernel)
  have t4 : a 5 ∈ [3] := remove (a 5) 0 [0,3] d5 b4
  have b5 : a 22 ≠ 0 := exclude [2] (fun u v => edge r53 v u) (a 22) (a 18) 0 t0 c53 (by decide +kernel)
  have t5 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b5
  have b6 : a 21 ≠ 0 := exclude [2] (edge r60) (a 21) (a 22) 0 t5 c60 (by decide +kernel)
  have t6 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_183
