import PartitionData205_114
namespace PartitionCover205_114
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d13 : a 13 ∈ [0,1,6,7])
    (d9 : a 9 ∈ [0,3])
    (d10 : a 10 ∈ [0,2,18,20])
    (d11 : a 11 ∈ [0,18])
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    : a 13 ∈ [0,6] ∧ a 10 ∈ [0,18] := by
  have b0 : a 13 ≠ 1 := exclude [0,3] (fun u v => edge r24 v u) (a 13) (a 9) 1 d9 c24 (by decide +kernel)
  have t0 : a 13 ∈ [0,6,7] := remove (a 13) 1 [0,1,6,7] d13 b0
  have b1 : a 13 ≠ 7 := exclude [0,3] (fun u v => edge r24 v u) (a 13) (a 9) 7 d9 c24 (by decide +kernel)
  have t1 : a 13 ∈ [0,6] := remove (a 13) 7 [0,6,7] t0 b1
  have b2 : a 10 ≠ 2 := exclude [0,18] (edge r25) (a 10) (a 11) 2 d11 c25 (by decide +kernel)
  have t2 : a 10 ∈ [0,18,20] := remove (a 10) 2 [0,2,18,20] d10 b2
  have b3 : a 10 ≠ 20 := exclude [0,18] (edge r25) (a 10) (a 11) 20 d11 c25 (by decide +kernel)
  have t3 : a 10 ∈ [0,18] := remove (a 10) 20 [0,18,20] t2 b3
  exact And.intro t1 (t3)

theorem chunk9 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,3])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,6])
    (d10 : a 10 ∈ [0,18])
    (d7 : a 7 ∈ [0,18])
    (d4 : a 4 ∈ [0,3])
    (d12 : a 12 ∈ [0,18])
    (d5 : a 5 ∈ [0,3])
    (d13 : a 13 ∈ [0,6])
    (d14 : a 14 ∈ [0,6])
    (d15 : a 15 ∈ [0,6])
    (d8 : a 8 ∈ [0,3])
    (d9 : a 9 ∈ [0,3])
    (d11 : a 11 ∈ [0,18])
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 5 ∈ [0] ∧ a 13 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 11 ∈ [0] := by
  have b0 : a 3 ≠ 3 := exclude [0] (fun u v => edge r7 v u) (a 3) (a 2) 3 d2 c7 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 3 [0,3] d3 b0
  have b1 : a 6 ≠ 6 := exclude [0] (fun u v => edge r8 v u) (a 6) (a 2) 6 d2 c8 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 6 [0,6] d6 b1
  have b2 : a 10 ≠ 18 := exclude [0] (fun u v => edge r9 v u) (a 10) (a 2) 18 d2 c9 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 18 [0,18] d10 b2
  have b3 : a 7 ≠ 18 := exclude [0] (fun u v => edge r10 v u) (a 7) (a 3) 18 t0 c10 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 18 [0,18] d7 b3
  have b4 : a 4 ≠ 3 := exclude [0] (edge r13) (a 4) (a 6) 3 t1 c13 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 3 [0,3] d4 b4
  have b5 : a 12 ≠ 18 := exclude [0] (fun u v => edge r14 v u) (a 12) (a 4) 18 t4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 18 [0,18] d12 b5
  have b6 : a 5 ≠ 3 := exclude [0] (edge r15) (a 5) (a 7) 3 t3 c15 (by decide +kernel)
  have t6 : a 5 ∈ [0] := remove (a 5) 3 [0,3] d5 b6
  have b7 : a 13 ≠ 6 := exclude [0] (fun u v => edge r16 v u) (a 13) (a 5) 6 t6 c16 (by decide +kernel)
  have t7 : a 13 ∈ [0] := remove (a 13) 6 [0,6] d13 b7
  have b8 : a 14 ≠ 6 := exclude [0] (fun u v => edge r18 v u) (a 14) (a 6) 6 t1 c18 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 6 [0,6] d14 b8
  have b9 : a 15 ≠ 6 := exclude [0] (fun u v => edge r19 v u) (a 15) (a 7) 6 t3 c19 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 6 [0,6] d15 b9
  have b10 : a 8 ≠ 3 := exclude [0] (edge r21) (a 8) (a 10) 3 t2 c21 (by decide +kernel)
  have t10 : a 8 ∈ [0] := remove (a 8) 3 [0,3] d8 b10
  have b11 : a 9 ≠ 3 := exclude [0] (edge r24) (a 9) (a 13) 3 t7 c24 (by decide +kernel)
  have t11 : a 9 ∈ [0] := remove (a 9) 3 [0,3] d9 b11
  have b12 : a 11 ≠ 18 := exclude [0] (fun u v => edge r25 v u) (a 11) (a 10) 18 t2 c25 (by decide +kernel)
  have t12 : a 11 ∈ [0] := remove (a 11) 18 [0,18] d11 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))

theorem chunk10 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,3])
    (d2 : a 2 ∈ [6])
    (d6 : a 6 ∈ [0,6])
    (d10 : a 10 ∈ [0,18])
    (d7 : a 7 ∈ [0,18])
    (d4 : a 4 ∈ [0,3])
    (d12 : a 12 ∈ [0,18])
    (d5 : a 5 ∈ [0,3])
    (d13 : a 13 ∈ [0,6])
    (d14 : a 14 ∈ [0,6])
    (d15 : a 15 ∈ [0,6])
    (d8 : a 8 ∈ [0,3])
    (d9 : a 9 ∈ [0,3])
    (d11 : a 11 ∈ [0,18])
    (c7 : edge r7 (a 2) (a 3)=true)
    (c8 : edge r8 (a 2) (a 6)=true)
    (c9 : edge r9 (a 2) (a 10)=true)
    (c10 : edge r10 (a 3) (a 7)=true)
    (c13 : edge r13 (a 4) (a 6)=true)
    (c14 : edge r14 (a 4) (a 12)=true)
    (c15 : edge r15 (a 5) (a 7)=true)
    (c16 : edge r16 (a 5) (a 13)=true)
    (c18 : edge r18 (a 6) (a 14)=true)
    (c19 : edge r19 (a 7) (a 15)=true)
    (c21 : edge r21 (a 8) (a 10)=true)
    (c24 : edge r24 (a 9) (a 13)=true)
    (c25 : edge r25 (a 10) (a 11)=true)
    : a 3 ∈ [3] ∧ a 6 ∈ [6] ∧ a 10 ∈ [18] ∧ a 7 ∈ [18] ∧ a 4 ∈ [3] ∧ a 12 ∈ [18] ∧ a 5 ∈ [3] ∧ a 13 ∈ [6] ∧ a 14 ∈ [6] ∧ a 15 ∈ [6] ∧ a 8 ∈ [3] ∧ a 9 ∈ [3] ∧ a 11 ∈ [18] := by
  have b0 : a 3 ≠ 0 := exclude [6] (fun u v => edge r7 v u) (a 3) (a 2) 0 d2 c7 (by decide +kernel)
  have t0 : a 3 ∈ [3] := remove (a 3) 0 [0,3] d3 b0
  have b1 : a 6 ≠ 0 := exclude [6] (fun u v => edge r8 v u) (a 6) (a 2) 0 d2 c8 (by decide +kernel)
  have t1 : a 6 ∈ [6] := remove (a 6) 0 [0,6] d6 b1
  have b2 : a 10 ≠ 0 := exclude [6] (fun u v => edge r9 v u) (a 10) (a 2) 0 d2 c9 (by decide +kernel)
  have t2 : a 10 ∈ [18] := remove (a 10) 0 [0,18] d10 b2
  have b3 : a 7 ≠ 0 := exclude [3] (fun u v => edge r10 v u) (a 7) (a 3) 0 t0 c10 (by decide +kernel)
  have t3 : a 7 ∈ [18] := remove (a 7) 0 [0,18] d7 b3
  have b4 : a 4 ≠ 0 := exclude [6] (edge r13) (a 4) (a 6) 0 t1 c13 (by decide +kernel)
  have t4 : a 4 ∈ [3] := remove (a 4) 0 [0,3] d4 b4
  have b5 : a 12 ≠ 0 := exclude [3] (fun u v => edge r14 v u) (a 12) (a 4) 0 t4 c14 (by decide +kernel)
  have t5 : a 12 ∈ [18] := remove (a 12) 0 [0,18] d12 b5
  have b6 : a 5 ≠ 0 := exclude [18] (edge r15) (a 5) (a 7) 0 t3 c15 (by decide +kernel)
  have t6 : a 5 ∈ [3] := remove (a 5) 0 [0,3] d5 b6
  have b7 : a 13 ≠ 0 := exclude [3] (fun u v => edge r16 v u) (a 13) (a 5) 0 t6 c16 (by decide +kernel)
  have t7 : a 13 ∈ [6] := remove (a 13) 0 [0,6] d13 b7
  have b8 : a 14 ≠ 0 := exclude [6] (fun u v => edge r18 v u) (a 14) (a 6) 0 t1 c18 (by decide +kernel)
  have t8 : a 14 ∈ [6] := remove (a 14) 0 [0,6] d14 b8
  have b9 : a 15 ≠ 0 := exclude [18] (fun u v => edge r19 v u) (a 15) (a 7) 0 t3 c19 (by decide +kernel)
  have t9 : a 15 ∈ [6] := remove (a 15) 0 [0,6] d15 b9
  have b10 : a 8 ≠ 0 := exclude [18] (edge r21) (a 8) (a 10) 0 t2 c21 (by decide +kernel)
  have t10 : a 8 ∈ [3] := remove (a 8) 0 [0,3] d8 b10
  have b11 : a 9 ≠ 0 := exclude [6] (edge r24) (a 9) (a 13) 0 t7 c24 (by decide +kernel)
  have t11 : a 9 ∈ [3] := remove (a 9) 0 [0,3] d9 b11
  have b12 : a 11 ≠ 0 := exclude [18] (fun u v => edge r25 v u) (a 11) (a 10) 0 t2 c25 (by decide +kernel)
  have t12 : a 11 ∈ [18] := remove (a 11) 0 [0,18] d11 b12
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (t12))))))))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
end PartitionCover205_114
