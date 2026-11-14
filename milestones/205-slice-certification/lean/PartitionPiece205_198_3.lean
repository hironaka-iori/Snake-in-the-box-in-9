import PartitionData205_198
namespace PartitionCover205_198
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17])
    (d22 : a 22 ∈ [0,3])
    (d23 : a 23 ∈ [0,1,4,5])
    (d31 : a 31 ∈ [0,1,6,8,9,11])
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 30 ∈ [0,2,4,6] ∧ a 23 ∈ [0,1] ∧ a 31 ∈ [0,1,11] := by
  have b0 : a 30 ≠ 7 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 7 d22 c66 (by decide +kernel)
  have t0 : a 30 ∈ [0,2,4,6,8,9,10,11,12,13,14,15,16,17] := remove (a 30) 7 [0,2,4,6,7,8,9,10,11,12,13,14,15,16,17] d30 b0
  have b1 : a 30 ≠ 8 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 8 d22 c66 (by decide +kernel)
  have t1 : a 30 ∈ [0,2,4,6,9,10,11,12,13,14,15,16,17] := remove (a 30) 8 [0,2,4,6,8,9,10,11,12,13,14,15,16,17] t0 b1
  have b2 : a 30 ≠ 9 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 9 d22 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0,2,4,6,10,11,12,13,14,15,16,17] := remove (a 30) 9 [0,2,4,6,9,10,11,12,13,14,15,16,17] t1 b2
  have b3 : a 30 ≠ 10 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 10 d22 c66 (by decide +kernel)
  have t3 : a 30 ∈ [0,2,4,6,11,12,13,14,15,16,17] := remove (a 30) 10 [0,2,4,6,10,11,12,13,14,15,16,17] t2 b3
  have b4 : a 30 ≠ 11 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 11 d22 c66 (by decide +kernel)
  have t4 : a 30 ∈ [0,2,4,6,12,13,14,15,16,17] := remove (a 30) 11 [0,2,4,6,11,12,13,14,15,16,17] t3 b4
  have b5 : a 30 ≠ 12 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 12 d22 c66 (by decide +kernel)
  have t5 : a 30 ∈ [0,2,4,6,13,14,15,16,17] := remove (a 30) 12 [0,2,4,6,12,13,14,15,16,17] t4 b5
  have b6 : a 30 ≠ 13 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 13 d22 c66 (by decide +kernel)
  have t6 : a 30 ∈ [0,2,4,6,14,15,16,17] := remove (a 30) 13 [0,2,4,6,13,14,15,16,17] t5 b6
  have b7 : a 30 ≠ 14 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 14 d22 c66 (by decide +kernel)
  have t7 : a 30 ∈ [0,2,4,6,15,16,17] := remove (a 30) 14 [0,2,4,6,14,15,16,17] t6 b7
  have b8 : a 30 ≠ 15 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 15 d22 c66 (by decide +kernel)
  have t8 : a 30 ∈ [0,2,4,6,16,17] := remove (a 30) 15 [0,2,4,6,15,16,17] t7 b8
  have b9 : a 30 ≠ 16 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 16 d22 c66 (by decide +kernel)
  have t9 : a 30 ∈ [0,2,4,6,17] := remove (a 30) 16 [0,2,4,6,16,17] t8 b9
  have b10 : a 30 ≠ 17 := exclude [0,3] (fun u v => edge r66 v u) (a 30) (a 22) 17 d22 c66 (by decide +kernel)
  have t10 : a 30 ∈ [0,2,4,6] := remove (a 30) 17 [0,2,4,6,17] t9 b10
  have b11 : a 23 ≠ 4 := exclude [0,1,6,8,9,11] (edge r67) (a 23) (a 31) 4 d31 c67 (by decide +kernel)
  have t11 : a 23 ∈ [0,1,5] := remove (a 23) 4 [0,1,4,5] d23 b11
  have b12 : a 23 ≠ 5 := exclude [0,1,6,8,9,11] (edge r67) (a 23) (a 31) 5 d31 c67 (by decide +kernel)
  have t12 : a 23 ∈ [0,1] := remove (a 23) 5 [0,1,5] t11 b12
  have b13 : a 31 ≠ 6 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 6 t12 c67 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,8,9,11] := remove (a 31) 6 [0,1,6,8,9,11] d31 b13
  have b14 : a 31 ≠ 8 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 8 t12 c67 (by decide +kernel)
  have t14 : a 31 ∈ [0,1,9,11] := remove (a 31) 8 [0,1,8,9,11] t13 b14
  have b15 : a 31 ≠ 9 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 9 t12 c67 (by decide +kernel)
  have t15 : a 31 ∈ [0,1,11] := remove (a 31) 9 [0,1,9,11] t14 b15
  exact And.intro t10 (And.intro t12 (t15))

theorem chunk13 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,1,11])
    (d23 : a 23 ∈ [0,1])
    (d24 : a 24 ∈ [0,1,6,7])
    (d25 : a 25 ∈ [0,1])
    (d30 : a 30 ∈ [0,2,4,6])
    (d26 : a 26 ∈ [0,4])
    (d13 : a 13 ∈ [0,1,4,5])
    (d29 : a 29 ∈ [0,6])
    (d19 : a 19 ∈ [0,1,4,5])
    (d18 : a 18 ∈ [0])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 31 ∈ [0,1] ∧ a 24 ∈ [0,6] ∧ a 30 ∈ [0,4] ∧ a 13 ∈ [0,4] ∧ a 19 ∈ [0,1] := by
  have b0 : a 31 ≠ 11 := exclude [0,1] (fun u v => edge r67 v u) (a 31) (a 23) 11 d23 c67 (by decide +kernel)
  have t0 : a 31 ∈ [0,1] := remove (a 31) 11 [0,1,11] d31 b0
  have b1 : a 24 ≠ 1 := exclude [0,1] (edge r68) (a 24) (a 25) 1 d25 c68 (by decide +kernel)
  have t1 : a 24 ∈ [0,6,7] := remove (a 24) 1 [0,1,6,7] d24 b1
  have b2 : a 24 ≠ 7 := exclude [0,1] (edge r68) (a 24) (a 25) 7 d25 c68 (by decide +kernel)
  have t2 : a 24 ∈ [0,6] := remove (a 24) 7 [0,6,7] t1 b2
  have b3 : a 30 ≠ 2 := exclude [0,4] (fun u v => edge r74 v u) (a 30) (a 26) 2 d26 c74 (by decide +kernel)
  have t3 : a 30 ∈ [0,4,6] := remove (a 30) 2 [0,2,4,6] d30 b3
  have b4 : a 30 ≠ 6 := exclude [0,4] (fun u v => edge r74 v u) (a 30) (a 26) 6 d26 c74 (by decide +kernel)
  have t4 : a 30 ∈ [0,4] := remove (a 30) 6 [0,4,6] t3 b4
  have b5 : a 13 ≠ 1 := exclude [0,6] (edge r44) (a 13) (a 29) 1 d29 c44 (by decide +kernel)
  have t5 : a 13 ∈ [0,4,5] := remove (a 13) 1 [0,1,4,5] d13 b5
  have b6 : a 13 ≠ 5 := exclude [0,6] (edge r44) (a 13) (a 29) 5 d29 c44 (by decide +kernel)
  have t6 : a 13 ∈ [0,4] := remove (a 13) 5 [0,4,5] t5 b6
  have b7 : a 19 ≠ 4 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 4 d18 c55 (by decide +kernel)
  have t7 : a 19 ∈ [0,1,5] := remove (a 19) 4 [0,1,4,5] d19 b7
  have b8 : a 19 ≠ 5 := exclude [0] (fun u v => edge r55 v u) (a 19) (a 18) 5 d18 c55 (by decide +kernel)
  have t8 : a 19 ∈ [0,1] := remove (a 19) 5 [0,1,5] t7 b8
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (t8))))

theorem chunk14 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,2])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d5 : a 5 ∈ [0,2])
    (d13 : a 13 ∈ [0,4])
    (d21 : a 21 ∈ [0,6])
    (d15 : a 15 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d24 : a 24 ∈ [0,6])
    (d9 : a 9 ∈ [0,1])
    (d26 : a 26 ∈ [0,4])
    (d27 : a 27 ∈ [0,1])
    (d16 : a 16 ∈ [0,3])
    (d17 : a 17 ∈ [0,6])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 3 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 5 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 15 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0] ∧ a 9 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 10 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b1
  have b2 : a 7 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 1 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b2
  have b3 : a 11 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 1 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b3
  have b4 : a 5 ≠ 2 := exclude [0] (edge r20) (a 5) (a 7) 2 t2 c20 (by decide +kernel)
  have t4 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b4
  have b5 : a 13 ≠ 4 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 4 t4 c21 (by decide +kernel)
  have t5 : a 13 ∈ [0] := remove (a 13) 4 [0,4] d13 b5
  have b6 : a 21 ≠ 6 := exclude [0] (fun u v => edge r22 v u) (a 21) (a 5) 6 t4 c22 (by decide +kernel)
  have t6 : a 21 ∈ [0] := remove (a 21) 6 [0,6] d21 b6
  have b7 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 t2 c26 (by decide +kernel)
  have t7 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b7
  have b8 : a 8 ≠ 1 := exclude [0] (edge r29) (a 8) (a 10) 1 t1 c29 (by decide +kernel)
  have t8 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b8
  have b9 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 t8 c30 (by decide +kernel)
  have t9 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b9
  have b10 : a 24 ≠ 6 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 6 t8 c31 (by decide +kernel)
  have t10 : a 24 ∈ [0] := remove (a 24) 6 [0,6] d24 b10
  have b11 : a 9 ≠ 1 := exclude [0] (edge r32) (a 9) (a 11) 1 t3 c32 (by decide +kernel)
  have t11 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b11
  have b12 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t1 c37 (by decide +kernel)
  have t12 : a 26 ∈ [0] := remove (a 26) 4 [0,4] d26 b12
  have b13 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 t3 c39 (by decide +kernel)
  have t13 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b13
  have b14 : a 16 ≠ 3 := exclude [0] (edge r51) (a 16) (a 24) 3 t10 c51 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 3 [0,3] d16 b14
  have b15 : a 17 ≠ 6 := exclude [0] (edge r53) (a 17) (a 21) 6 t6 c53 (by decide +kernel)
  have t15 : a 17 ∈ [0] := remove (a 17) 6 [0,6] d17 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d29 : a 29 ∈ [0,6])
    (d21 : a 21 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d30 : a 30 ∈ [0,4])
    (d26 : a 26 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d5 : a 5 ∈ [0])
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [0,3])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    : a 19 ∈ [0] ∧ a 29 ∈ [0] ∧ a 25 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 4 ∈ [0] ∧ a 23 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 19 ≠ 1 := exclude [0] (edge r59) (a 19) (a 27) 1 d27 c59 (by decide +kernel)
  have t0 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b0
  have b1 : a 29 ≠ 6 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 6 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 6 [0,6] d29 b1
  have b2 : a 25 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 1 d24 c68 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b2
  have b3 : a 30 ≠ 4 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 4 d26 c74 (by decide +kernel)
  have t3 : a 30 ∈ [0] := remove (a 30) 4 [0,4] d30 b3
  have b4 : a 31 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 1 d27 c75 (by decide +kernel)
  have t4 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b4
  have b5 : a 4 ≠ 2 := exclude [0] (edge r16) (a 4) (a 5) 2 d5 c16 (by decide +kernel)
  have t5 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b5
  have b6 : a 23 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 1 t0 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b6
  have b7 : a 22 ≠ 3 := exclude [0] (edge r65) (a 22) (a 23) 3 t6 c65 (by decide +kernel)
  have t7 : a 22 ∈ [0] := remove (a 22) 3 [0,3] d22 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_198
