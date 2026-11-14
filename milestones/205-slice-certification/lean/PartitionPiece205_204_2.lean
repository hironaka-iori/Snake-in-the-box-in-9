import PartitionData205_204
namespace PartitionCover205_204
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,4])
    (d7 : a 7 ∈ [0,2])
    (d11 : a 11 ∈ [0,6])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,4])
    (d15 : a 15 ∈ [0,4])
    (d23 : a 23 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d27 : a 27 ∈ [0,4])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 5 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 25 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 4 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 4 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 4 [0,4] d6 b1
  have b2 : a 7 ≠ 2 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 2 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b2
  have b3 : a 11 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 6 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b3
  have b4 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t1 c17 (by decide +kernel)
  have t4 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b4
  have b5 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b5
  have b6 : a 5 ≠ 1 := exclude [0] (edge r20) (a 5) (a 7) 1 t2 c20 (by decide +kernel)
  have t6 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b6
  have b7 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 t1 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b7
  have b8 : a 22 ≠ 4 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 4 t1 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 4 [0,4] d22 b8
  have b9 : a 15 ≠ 4 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 4 t2 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 4 [0,4] d15 b9
  have b10 : a 23 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 2 t2 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b10
  have b11 : a 8 ≠ 2 := exclude [0] (edge r30) (a 8) (a 12) 2 t5 c30 (by decide +kernel)
  have t11 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b11
  have b12 : a 9 ≠ 1 := exclude [0] (edge r32) (a 9) (a 11) 1 t3 c32 (by decide +kernel)
  have t12 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b12
  have b13 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 t12 c33 (by decide +kernel)
  have t13 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b13
  have b14 : a 25 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 1 t12 c34 (by decide +kernel)
  have t14 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b14
  have b15 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 t3 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0] := remove (a 27) 4 [0,4] d27 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d21 : a 21 ∈ [0,1])
    (d26 : a 26 ∈ [0,2])
    (d27 : a 27 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 28 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 21 ∈ [0] ∧ a 26 ∈ [0] ∧ a 20 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b0
  have b1 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b1
  have b2 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b2
  have b3 : a 21 ≠ 1 := exclude [0] (edge r64) (a 21) (a 29) 1 t1 c64 (by decide +kernel)
  have t3 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b3
  have b4 : a 26 ≠ 2 := exclude [0] (edge r73) (a 26) (a 27) 2 d27 c73 (by decide +kernel)
  have t4 : a 26 ∈ [0] := remove (a 26) 2 [0,2] d26 b4
  have b5 : a 20 ≠ 1 := exclude [0] (edge r60) (a 20) (a 21) 1 t3 c60 (by decide +kernel)
  have t5 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b5
  have b6 : a 16 ≠ 1 := exclude [0] (edge r50) (a 16) (a 20) 1 t5 c50 (by decide +kernel)
  have t6 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b6
  have b7 : a 17 ≠ 2 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 2 t6 c48 (by decide +kernel)
  have t7 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk10 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [2])
    (d6 : a 6 ∈ [0,4])
    (d7 : a 7 ∈ [0,2])
    (d11 : a 11 ∈ [0,6])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,4])
    (d15 : a 15 ∈ [0,4])
    (d23 : a 23 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d25 : a 25 ∈ [0,1])
    (d27 : a 27 ∈ [0,4])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 3 ∈ [1] ∧ a 6 ∈ [4] ∧ a 7 ∈ [2] ∧ a 11 ∈ [6] ∧ a 4 ∈ [1] ∧ a 12 ∈ [1] ∧ a 5 ∈ [1] ∧ a 14 ∈ [1] ∧ a 22 ∈ [4] ∧ a 15 ∈ [4] ∧ a 23 ∈ [2] ∧ a 8 ∈ [2] ∧ a 9 ∈ [1] ∧ a 13 ∈ [1] ∧ a 25 ∈ [1] ∧ a 27 ∈ [4] := by
  have b0 : a 3 ≠ 0 := exclude [2] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 6 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 6) (a 2) 0 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [4] := remove (a 6) 0 [0,4] d6 b1
  have b2 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b2
  have b3 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [6] := remove (a 11) 0 [0,6] d11 b3
  have b4 : a 4 ≠ 0 := exclude [4] (edge r17) (a 4) (a 6) 0 t1 c17 (by decide +kernel)
  have t4 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b4
  have b5 : a 12 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 12) (a 4) 0 t4 c18 (by decide +kernel)
  have t5 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b5
  have b6 : a 5 ≠ 0 := exclude [2] (edge r20) (a 5) (a 7) 0 t2 c20 (by decide +kernel)
  have t6 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b6
  have b7 : a 14 ≠ 0 := exclude [4] (fun u v => edge r24 v u) (a 14) (a 6) 0 t1 c24 (by decide +kernel)
  have t7 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b7
  have b8 : a 22 ≠ 0 := exclude [4] (fun u v => edge r25 v u) (a 22) (a 6) 0 t1 c25 (by decide +kernel)
  have t8 : a 22 ∈ [4] := remove (a 22) 0 [0,4] d22 b8
  have b9 : a 15 ≠ 0 := exclude [2] (fun u v => edge r26 v u) (a 15) (a 7) 0 t2 c26 (by decide +kernel)
  have t9 : a 15 ∈ [4] := remove (a 15) 0 [0,4] d15 b9
  have b10 : a 23 ≠ 0 := exclude [2] (fun u v => edge r27 v u) (a 23) (a 7) 0 t2 c27 (by decide +kernel)
  have t10 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b10
  have b11 : a 8 ≠ 0 := exclude [1] (edge r30) (a 8) (a 12) 0 t5 c30 (by decide +kernel)
  have t11 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b11
  have b12 : a 9 ≠ 0 := exclude [6] (edge r32) (a 9) (a 11) 0 t3 c32 (by decide +kernel)
  have t12 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b12
  have b13 : a 13 ≠ 0 := exclude [1] (fun u v => edge r33 v u) (a 13) (a 9) 0 t12 c33 (by decide +kernel)
  have t13 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b13
  have b14 : a 25 ≠ 0 := exclude [1] (fun u v => edge r34 v u) (a 25) (a 9) 0 t12 c34 (by decide +kernel)
  have t14 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b14
  have b15 : a 27 ≠ 0 := exclude [6] (fun u v => edge r39 v u) (a 27) (a 11) 0 t3 c39 (by decide +kernel)
  have t15 : a 27 ∈ [4] := remove (a 27) 0 [0,4] d27 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk11 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1])
    (d12 : a 12 ∈ [1])
    (d29 : a 29 ∈ [0,1])
    (d13 : a 13 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [1])
    (d21 : a 21 ∈ [0,1])
    (d26 : a 26 ∈ [0,2])
    (d27 : a 27 ∈ [4])
    (d20 : a 20 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 28 ∈ [1] ∧ a 29 ∈ [1] ∧ a 30 ∈ [1] ∧ a 21 ∈ [1] ∧ a 26 ∈ [2] ∧ a 20 ∈ [1] ∧ a 16 ∈ [1] ∧ a 17 ∈ [2] := by
  have b0 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b0
  have b1 : a 29 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 29) (a 13) 0 d13 c44 (by decide +kernel)
  have t1 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b1
  have b2 : a 30 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t2 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b2
  have b3 : a 21 ≠ 0 := exclude [1] (edge r64) (a 21) (a 29) 0 t1 c64 (by decide +kernel)
  have t3 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b3
  have b4 : a 26 ≠ 0 := exclude [4] (edge r73) (a 26) (a 27) 0 d27 c73 (by decide +kernel)
  have t4 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b4
  have b5 : a 20 ≠ 0 := exclude [1] (edge r60) (a 20) (a 21) 0 t3 c60 (by decide +kernel)
  have t5 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b5
  have b6 : a 16 ≠ 0 := exclude [1] (edge r50) (a 16) (a 20) 0 t5 c50 (by decide +kernel)
  have t6 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b6
  have b7 : a 17 ≠ 0 := exclude [1] (fun u v => edge r48 v u) (a 17) (a 16) 0 t6 c48 (by decide +kernel)
  have t7 : a 17 ∈ [2] := remove (a 17) 0 [0,2] d17 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_204
