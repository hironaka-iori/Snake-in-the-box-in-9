import PartitionData205_182
namespace PartitionCover205_182
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d8 : a 8 ∈ [0,6])
    (d24 : a 24 ∈ [0,4])
    (d13 : a 13 ∈ [0,3])
    (d28 : a 28 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d29 : a 29 ∈ [0,6])
    (d16 : a 16 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 8 ∈ [0] ∧ a 24 ∈ [0] ∧ a 13 ∈ [0] ∧ a 28 ∈ [0] ∧ a 15 ∈ [0] ∧ a 29 ∈ [0] ∧ a 16 ∈ [0] ∧ a 30 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b1
  have b2 : a 10 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b2
  have b3 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b3
  have b4 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t1 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b4
  have b5 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b5
  have b6 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 t4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b6
  have b7 : a 8 ≠ 6 := exclude [0] (edge r29) (a 8) (a 10) 6 t2 c29 (by decide +kernel)
  have t7 : a 8 ∈ [0] := remove (a 8) 6 [0,6] d8 b7
  have b8 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 t7 c31 (by decide +kernel)
  have t8 : a 24 ∈ [0] := remove (a 24) 4 [0,4] d24 b8
  have b9 : a 13 ≠ 3 := exclude [0] (fun u v => edge r40 v u) (a 13) (a 12) 3 t5 c40 (by decide +kernel)
  have t9 : a 13 ∈ [0] := remove (a 13) 3 [0,3] d13 b9
  have b10 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t5 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b10
  have b11 : a 15 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 15) (a 13) 1 t9 c43 (by decide +kernel)
  have t11 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b11
  have b12 : a 29 ≠ 6 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 6 t9 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0] := remove (a 29) 6 [0,6] d29 b12
  have b13 : a 16 ≠ 1 := exclude [0] (edge r50) (a 16) (a 20) 1 t6 c50 (by decide +kernel)
  have t13 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b13
  have b14 : a 30 ≠ 2 := exclude [0] (fun u v => edge r77 v u) (a 30) (a 28) 2 t10 c77 (by decide +kernel)
  have t14 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b14
  have b15 : a 5 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 5) (a 4) 1 t4 c16 (by decide +kernel)
  have t15 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk17 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (c48 : edge r48 (a 16) (a 17)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 17 ∈ [0] ∧ a 25 ∈ [0] ∧ a 22 ∈ [0] ∧ a 26 ∈ [0] ∧ a 23 ∈ [0] ∧ a 19 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 17 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 1 d16 c48 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b0
  have b1 : a 25 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 1 t0 c54 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b1
  have b2 : a 22 ≠ 2 := exclude [0] (edge r66) (a 22) (a 30) 2 d30 c66 (by decide +kernel)
  have t2 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b2
  have b3 : a 26 ≠ 1 := exclude [0] (edge r74) (a 26) (a 30) 1 d30 c74 (by decide +kernel)
  have t3 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b3
  have b4 : a 23 ≠ 1 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 1 t2 c65 (by decide +kernel)
  have t4 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b4
  have b5 : a 19 ≠ 1 := exclude [0] (edge r58) (a 19) (a 23) 1 t4 c58 (by decide +kernel)
  have t5 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b5
  have b6 : a 27 ≠ 1 := exclude [0] (fun u v => edge r59 v u) (a 27) (a 19) 1 t5 c59 (by decide +kernel)
  have t6 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))

theorem chunk18 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d8 : a 8 ∈ [0,6])
    (d24 : a 24 ∈ [0,4])
    (d13 : a 13 ∈ [0,3])
    (d28 : a 28 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d29 : a 29 ∈ [0,6])
    (d16 : a 16 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 3 ∈ [1] ∧ a 6 ∈ [2] ∧ a 10 ∈ [2] ∧ a 11 ∈ [2] ∧ a 4 ∈ [1] ∧ a 12 ∈ [1] ∧ a 20 ∈ [1] ∧ a 8 ∈ [6] ∧ a 24 ∈ [4] ∧ a 13 ∈ [3] ∧ a 28 ∈ [1] ∧ a 15 ∈ [1] ∧ a 29 ∈ [6] ∧ a 16 ∈ [1] ∧ a 30 ∈ [2] ∧ a 5 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 6 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 6) (a 2) 0 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b1
  have b2 : a 10 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 10) (a 2) 0 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b2
  have b3 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b3
  have b4 : a 4 ≠ 0 := exclude [2] (edge r17) (a 4) (a 6) 0 t1 c17 (by decide +kernel)
  have t4 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b4
  have b5 : a 12 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 12) (a 4) 0 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b5
  have b6 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t4 c19 (by decide +kernel)
  have t6 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b6
  have b7 : a 8 ≠ 0 := exclude [2] (edge r29) (a 8) (a 10) 0 t2 c29 (by decide +kernel)
  have t7 : a 8 ∈ [6] := remove (a 8) 0 [0,6] d8 b7
  have b8 : a 24 ≠ 0 := exclude [6] (fun u v => edge r31 v u) (a 24) (a 8) 0 t7 c31 (by decide +kernel)
  have t8 : a 24 ∈ [4] := remove (a 24) 0 [0,4] d24 b8
  have b9 : a 13 ≠ 0 := exclude [1] (fun u v => edge r40 v u) (a 13) (a 12) 0 t5 c40 (by decide +kernel)
  have t9 : a 13 ∈ [3] := remove (a 13) 0 [0,3] d13 b9
  have b10 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 t5 c42 (by decide +kernel)
  have t10 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b10
  have b11 : a 15 ≠ 0 := exclude [3] (fun u v => edge r43 v u) (a 15) (a 13) 0 t9 c43 (by decide +kernel)
  have t11 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b11
  have b12 : a 29 ≠ 0 := exclude [3] (fun u v => edge r44 v u) (a 29) (a 13) 0 t9 c44 (by decide +kernel)
  have t12 : a 29 ∈ [6] := remove (a 29) 0 [0,6] d29 b12
  have b13 : a 16 ≠ 0 := exclude [1] (edge r50) (a 16) (a 20) 0 t6 c50 (by decide +kernel)
  have t13 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b13
  have b14 : a 30 ≠ 0 := exclude [1] (fun u v => edge r77 v u) (a 30) (a 28) 0 t10 c77 (by decide +kernel)
  have t14 : a 30 ∈ [2] := remove (a 30) 0 [0,2] d30 b14
  have b15 : a 5 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 5) (a 4) 0 t4 c16 (by decide +kernel)
  have t15 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk19 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1])
    (d16 : a 16 ∈ [1])
    (d25 : a 25 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d30 : a 30 ∈ [2])
    (d26 : a 26 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (c48 : edge r48 (a 16) (a 17)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 17 ∈ [1] ∧ a 25 ∈ [1] ∧ a 22 ∈ [2] ∧ a 26 ∈ [1] ∧ a 23 ∈ [1] ∧ a 19 ∈ [1] ∧ a 27 ∈ [1] := by
  have b0 : a 17 ≠ 0 := exclude [1] (fun u v => edge r48 v u) (a 17) (a 16) 0 d16 c48 (by decide +kernel)
  have t0 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b0
  have b1 : a 25 ≠ 0 := exclude [1] (fun u v => edge r54 v u) (a 25) (a 17) 0 t0 c54 (by decide +kernel)
  have t1 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b1
  have b2 : a 22 ≠ 0 := exclude [2] (edge r66) (a 22) (a 30) 0 d30 c66 (by decide +kernel)
  have t2 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b2
  have b3 : a 26 ≠ 0 := exclude [2] (edge r74) (a 26) (a 30) 0 d30 c74 (by decide +kernel)
  have t3 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b3
  have b4 : a 23 ≠ 0 := exclude [2] (fun u v => edge r65 v u) (a 23) (a 22) 0 t2 c65 (by decide +kernel)
  have t4 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b4
  have b5 : a 19 ≠ 0 := exclude [1] (edge r58) (a 19) (a 23) 0 t4 c58 (by decide +kernel)
  have t5 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b5
  have b6 : a 27 ≠ 0 := exclude [1] (fun u v => edge r59 v u) (a 27) (a 19) 0 t5 c59 (by decide +kernel)
  have t6 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk16
#print axioms chunk17
#print axioms chunk18
#print axioms chunk19
end PartitionCover205_182
