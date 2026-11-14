import PartitionData205_154
namespace PartitionCover205_154
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2,3,4,5,6,7,8,9,10,11])
    (d5 : a 5 ∈ [0,6])
    (d13 : a 13 ∈ [0,1,2,3,4,5,6,7])
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    : a 7 ∈ [0,6] ∧ a 13 ∈ [0,4] := by
  have b0 : a 7 ≠ 1 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 1 d5 c15 (by decide +kernel)
  have t0 : a 7 ∈ [0,2,3,4,5,6,7,8,9,10,11] := remove (a 7) 1 [0,1,2,3,4,5,6,7,8,9,10,11] d7 b0
  have b1 : a 7 ≠ 2 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 2 d5 c15 (by decide +kernel)
  have t1 : a 7 ∈ [0,3,4,5,6,7,8,9,10,11] := remove (a 7) 2 [0,2,3,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 7 ≠ 3 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 3 d5 c15 (by decide +kernel)
  have t2 : a 7 ∈ [0,4,5,6,7,8,9,10,11] := remove (a 7) 3 [0,3,4,5,6,7,8,9,10,11] t1 b2
  have b3 : a 7 ≠ 4 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 4 d5 c15 (by decide +kernel)
  have t3 : a 7 ∈ [0,5,6,7,8,9,10,11] := remove (a 7) 4 [0,4,5,6,7,8,9,10,11] t2 b3
  have b4 : a 7 ≠ 5 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 5 d5 c15 (by decide +kernel)
  have t4 : a 7 ∈ [0,6,7,8,9,10,11] := remove (a 7) 5 [0,5,6,7,8,9,10,11] t3 b4
  have b5 : a 7 ≠ 7 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 7 d5 c15 (by decide +kernel)
  have t5 : a 7 ∈ [0,6,8,9,10,11] := remove (a 7) 7 [0,6,7,8,9,10,11] t4 b5
  have b6 : a 7 ≠ 8 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 8 d5 c15 (by decide +kernel)
  have t6 : a 7 ∈ [0,6,9,10,11] := remove (a 7) 8 [0,6,8,9,10,11] t5 b6
  have b7 : a 7 ≠ 9 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 9 d5 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0,6,10,11] := remove (a 7) 9 [0,6,9,10,11] t6 b7
  have b8 : a 7 ≠ 10 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 10 d5 c15 (by decide +kernel)
  have t8 : a 7 ∈ [0,6,11] := remove (a 7) 10 [0,6,10,11] t7 b8
  have b9 : a 7 ≠ 11 := exclude [0,6] (fun u v => edge r15 v u) (a 7) (a 5) 11 d5 c15 (by decide +kernel)
  have t9 : a 7 ∈ [0,6] := remove (a 7) 11 [0,6,11] t8 b9
  have b10 : a 13 ≠ 1 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 1 d5 c16 (by decide +kernel)
  have t10 : a 13 ∈ [0,2,3,4,5,6,7] := remove (a 13) 1 [0,1,2,3,4,5,6,7] d13 b10
  have b11 : a 13 ≠ 2 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 2 d5 c16 (by decide +kernel)
  have t11 : a 13 ∈ [0,3,4,5,6,7] := remove (a 13) 2 [0,2,3,4,5,6,7] t10 b11
  have b12 : a 13 ≠ 3 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 3 d5 c16 (by decide +kernel)
  have t12 : a 13 ∈ [0,4,5,6,7] := remove (a 13) 3 [0,3,4,5,6,7] t11 b12
  have b13 : a 13 ≠ 5 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 5 d5 c16 (by decide +kernel)
  have t13 : a 13 ∈ [0,4,6,7] := remove (a 13) 5 [0,4,5,6,7] t12 b13
  have b14 : a 13 ≠ 6 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 6 d5 c16 (by decide +kernel)
  have t14 : a 13 ∈ [0,4,7] := remove (a 13) 6 [0,4,6,7] t13 b14
  have b15 : a 13 ≠ 7 := exclude [0,6] (fun u v => edge r16 v u) (a 13) (a 5) 7 d5 c16 (by decide +kernel)
  have t15 : a 13 ∈ [0,4] := remove (a 13) 7 [0,4,7] t14 b15
  exact And.intro t9 (t15)

theorem chunk5 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,2,3,4,5,6,7])
    (d6 : a 6 ∈ [0,4])
    (d15 : a 15 ∈ [0,1,2,3,4,5,6,7])
    (d7 : a 7 ∈ [0,6])
    (d8 : a 8 ∈ [0,1,8,9,16,17,24,25])
    (d9 : a 9 ∈ [0])
    (d10 : a 10 ∈ [0,3,8,11])
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c20 : edge r20 (a 8) (a 9)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    : a 14 ∈ [0,4] ∧ a 15 ∈ [0,1,4,5] ∧ a 8 ∈ [0,16] := by
  have b0 : a 14 ≠ 1 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 1 d6 c18 (by decide +kernel)
  have t0 : a 14 ∈ [0,2,3,4,5,6,7] := remove (a 14) 1 [0,1,2,3,4,5,6,7] d14 b0
  have b1 : a 14 ≠ 2 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 2 d6 c18 (by decide +kernel)
  have t1 : a 14 ∈ [0,3,4,5,6,7] := remove (a 14) 2 [0,2,3,4,5,6,7] t0 b1
  have b2 : a 14 ≠ 3 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 3 d6 c18 (by decide +kernel)
  have t2 : a 14 ∈ [0,4,5,6,7] := remove (a 14) 3 [0,3,4,5,6,7] t1 b2
  have b3 : a 14 ≠ 5 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 5 d6 c18 (by decide +kernel)
  have t3 : a 14 ∈ [0,4,6,7] := remove (a 14) 5 [0,4,5,6,7] t2 b3
  have b4 : a 14 ≠ 6 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 6 d6 c18 (by decide +kernel)
  have t4 : a 14 ∈ [0,4,7] := remove (a 14) 6 [0,4,6,7] t3 b4
  have b5 : a 14 ≠ 7 := exclude [0,4] (fun u v => edge r18 v u) (a 14) (a 6) 7 d6 c18 (by decide +kernel)
  have t5 : a 14 ∈ [0,4] := remove (a 14) 7 [0,4,7] t4 b5
  have b6 : a 15 ≠ 2 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 2 d7 c19 (by decide +kernel)
  have t6 : a 15 ∈ [0,1,3,4,5,6,7] := remove (a 15) 2 [0,1,2,3,4,5,6,7] d15 b6
  have b7 : a 15 ≠ 3 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 3 d7 c19 (by decide +kernel)
  have t7 : a 15 ∈ [0,1,4,5,6,7] := remove (a 15) 3 [0,1,3,4,5,6,7] t6 b7
  have b8 : a 15 ≠ 6 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 6 d7 c19 (by decide +kernel)
  have t8 : a 15 ∈ [0,1,4,5,7] := remove (a 15) 6 [0,1,4,5,6,7] t7 b8
  have b9 : a 15 ≠ 7 := exclude [0,6] (fun u v => edge r19 v u) (a 15) (a 7) 7 d7 c19 (by decide +kernel)
  have t9 : a 15 ∈ [0,1,4,5] := remove (a 15) 7 [0,1,4,5,7] t8 b9
  have b10 : a 8 ≠ 1 := exclude [0] (edge r20) (a 8) (a 9) 1 d9 c20 (by decide +kernel)
  have t10 : a 8 ∈ [0,8,9,16,17,24,25] := remove (a 8) 1 [0,1,8,9,16,17,24,25] d8 b10
  have b11 : a 8 ≠ 9 := exclude [0] (edge r20) (a 8) (a 9) 9 d9 c20 (by decide +kernel)
  have t11 : a 8 ∈ [0,8,16,17,24,25] := remove (a 8) 9 [0,8,9,16,17,24,25] t10 b11
  have b12 : a 8 ≠ 17 := exclude [0] (edge r20) (a 8) (a 9) 17 d9 c20 (by decide +kernel)
  have t12 : a 8 ∈ [0,8,16,24,25] := remove (a 8) 17 [0,8,16,17,24,25] t11 b12
  have b13 : a 8 ≠ 25 := exclude [0] (edge r20) (a 8) (a 9) 25 d9 c20 (by decide +kernel)
  have t13 : a 8 ∈ [0,8,16,24] := remove (a 8) 25 [0,8,16,24,25] t12 b13
  have b14 : a 8 ≠ 8 := exclude [0,3,8,11] (edge r21) (a 8) (a 10) 8 d10 c21 (by decide +kernel)
  have t14 : a 8 ∈ [0,16,24] := remove (a 8) 8 [0,8,16,24] t13 b14
  have b15 : a 8 ≠ 24 := exclude [0,3,8,11] (edge r21) (a 8) (a 10) 24 d10 c21 (by decide +kernel)
  have t15 : a 8 ∈ [0,16] := remove (a 8) 24 [0,16,24] t14 b15
  exact And.intro t5 (And.intro t9 (t15))

theorem chunk6 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,3,8,11])
    (d8 : a 8 ∈ [0,16])
    (d15 : a 15 ∈ [0,1,4,5])
    (d13 : a 13 ∈ [0,4])
    (c21 : edge r21 (a 8) (a 10)=true)
    (c30 : edge r30 (a 13) (a 15)=true)
    : a 10 ∈ [0,8] ∧ a 15 ∈ [0,4] := by
  have b0 : a 10 ≠ 3 := exclude [0,16] (fun u v => edge r21 v u) (a 10) (a 8) 3 d8 c21 (by decide +kernel)
  have t0 : a 10 ∈ [0,8,11] := remove (a 10) 3 [0,3,8,11] d10 b0
  have b1 : a 10 ≠ 11 := exclude [0,16] (fun u v => edge r21 v u) (a 10) (a 8) 11 d8 c21 (by decide +kernel)
  have t1 : a 10 ∈ [0,8] := remove (a 10) 11 [0,8,11] t0 b1
  have b2 : a 15 ≠ 1 := exclude [0,4] (fun u v => edge r30 v u) (a 15) (a 13) 1 d13 c30 (by decide +kernel)
  have t2 : a 15 ∈ [0,4,5] := remove (a 15) 1 [0,1,4,5] d15 b2
  have b3 : a 15 ≠ 5 := exclude [0,4] (fun u v => edge r30 v u) (a 15) (a 13) 5 d13 c30 (by decide +kernel)
  have t3 : a 15 ∈ [0,4] := remove (a 15) 5 [0,4,5] t2 b3
  exact And.intro t1 (t3)

theorem chunk7 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,6])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0,4])
    (d7 : a 7 ∈ [0,6])
    (d11 : a 11 ∈ [0,1])
    (d4 : a 4 ∈ [0,4])
    (d12 : a 12 ∈ [0,4])
    (d13 : a 13 ∈ [0,4])
    (d14 : a 14 ∈ [0,4])
    (d15 : a 15 ∈ [0,4])
    (d10 : a 10 ∈ [0,8])
    (d8 : a 8 ∈ [0,16])
    (c4 : edge r4 (a 1) (a 3)=true)
    (c5 : edge r5 (a 1) (a 5)=true)
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c11 : edge r11 (a 3) (a 11)=true)
    (c12 : edge r12 (a 4) (a 5)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c26 : edge r26 (a 10) (a 14)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 10 ∈ [0] ∧ a 8 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 3) (a 1) 1 d1 c4 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 6 := exclude [0] (fun u v => edge r5 v u) (a 5) (a 1) 6 d1 c5 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 6 [0,6] d5 b1
  have b2 : a 2 ≠ 1 := exclude [0] (edge r7) (a 2) (a 3) 1 t0 c7 (by decide +kernel)
  have t2 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b2
  have b3 : a 6 ≠ 4 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 4 t2 c8 (by decide +kernel)
  have t3 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b3
  have b4 : a 7 ≠ 6 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 6 t0 c10 (by decide +kernel)
  have t4 : a 7 ∈ [0] := remove (a 7) 6 [0,6] d7 b4
  have b5 : a 11 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 11) (a 3) 1 t0 c11 (by decide +kernel)
  have t5 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b5
  have b6 : a 4 ≠ 4 := exclude [0] (edge r12) (a 4) (a 5) 4 t1 c12 (by decide +kernel)
  have t6 : a 4 ∈ [0] := remove (a 4) 4 [0,4] d4 b6
  have b7 : a 12 ≠ 4 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 4 t6 c14 (by decide +kernel)
  have t7 : a 12 ∈ [0] := remove (a 12) 4 [0,4] d12 b7
  have b8 : a 13 ≠ 4 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 4 t1 c16 (by decide +kernel)
  have t8 : a 13 ∈ [0] := remove (a 13) 4 [0,4] d13 b8
  have b9 : a 14 ≠ 4 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 4 t3 c18 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 4 [0,4] d14 b9
  have b10 : a 15 ≠ 4 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 4 t4 c19 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 4 [0,4] d15 b10
  have b11 : a 10 ≠ 8 := exclude [0] (edge r26) (a 10) (a 14) 8 t9 c26 (by decide +kernel)
  have t11 : a 10 ∈ [0] := remove (a 10) 8 [0,8] d10 b11
  have b12 : a 8 ≠ 16 := exclude [0] (edge r21) (a 8) (a 10) 16 t11 c21 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 16 [0,16] d8 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_154
