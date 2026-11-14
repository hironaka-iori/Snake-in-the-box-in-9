import PartitionData205_175
namespace PartitionCover205_175
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,3])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,4])
    (d17 : a 17 ∈ [0,1])
    (d4 : a 4 ∈ [0,3])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d14 : a 14 ∈ [0,3])
    (d22 : a 22 ∈ [0,1])
    (d15 : a 15 ∈ [0,13])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d11 : a 11 ∈ [0,6])
    (d27 : a 27 ∈ [0,3])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 4 ∈ [0] ∧ a 6 ∈ [0] ∧ a 12 ∈ [0] ∧ a 7 ∈ [0] ∧ a 14 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 24 ∈ [0] ∧ a 11 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 5 ≠ 3 := exclude [0] (fun u v => edge r6 v u) (a 5) (a 1) 3 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [0] := remove (a 5) 3 [0,3] d5 b0
  have b1 : a 9 ≠ 4 := exclude [0] (fun u v => edge r7 v u) (a 9) (a 1) 4 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 4 [0,4] d9 b1
  have b2 : a 17 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 17) (a 1) 1 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b2
  have b3 : a 4 ≠ 3 := exclude [0] (edge r16) (a 4) (a 5) 3 t0 c16 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 3 [0,3] d4 b3
  have b4 : a 6 ≠ 1 := exclude [0] (fun u v => edge r17 v u) (a 6) (a 4) 1 t3 c17 (by decide +kernel)
  have t4 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b4
  have b5 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t3 c18 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b5
  have b6 : a 7 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 7) (a 5) 2 t0 c20 (by decide +kernel)
  have t6 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b6
  have b7 : a 14 ≠ 3 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 3 t4 c24 (by decide +kernel)
  have t7 : a 14 ∈ [0] := remove (a 14) 3 [0,3] d14 b7
  have b8 : a 22 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 22) (a 6) 1 t4 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b8
  have b9 : a 15 ≠ 13 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 13 t6 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 13 [0,13] d15 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 t6 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b10
  have b11 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 t1 c28 (by decide +kernel)
  have t11 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b11
  have b12 : a 10 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 10) (a 8) 1 t11 c29 (by decide +kernel)
  have t12 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b12
  have b13 : a 24 ≠ 1 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 1 t11 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b13
  have b14 : a 11 ≠ 6 := exclude [0] (fun u v => edge r32 v u) (a 11) (a 9) 6 t1 c32 (by decide +kernel)
  have t14 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b14
  have b15 : a 27 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 3 t14 c39 (by decide +kernel)
  have t15 : a 27 ∈ [0] := remove (a 27) 3 [0,3] d27 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk13 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,3])
    (d12 : a 12 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d16 : a 16 ∈ [0,2])
    (d17 : a 17 ∈ [0])
    (d18 : a 18 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d31 : a 31 ∈ [0,3])
    (d27 : a 27 ∈ [0])
    (d29 : a 29 ∈ [0,6])
    (d3 : a 3 ∈ [0,2])
    (d7 : a 7 ∈ [0])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 28 ∈ [0] ∧ a 30 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] ∧ a 19 ∈ [0] ∧ a 31 ∈ [0] ∧ a 29 ∈ [0] ∧ a 3 ∈ [0] := by
  have b0 : a 28 ≠ 3 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [0] := remove (a 28) 3 [0,3] d28 b0
  have b1 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b1
  have b2 : a 16 ≠ 2 := exclude [0] (edge r48) (a 16) (a 17) 2 d17 c48 (by decide +kernel)
  have t2 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b2
  have b3 : a 18 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 2 t2 c49 (by decide +kernel)
  have t3 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b3
  have b4 : a 19 ≠ 1 := exclude [0] (fun u v => edge r52 v u) (a 19) (a 17) 1 d17 c52 (by decide +kernel)
  have t4 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b4
  have b5 : a 31 ≠ 3 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 3 d27 c75 (by decide +kernel)
  have t5 : a 31 ∈ [0] := remove (a 31) 3 [0,3] d31 b5
  have b6 : a 29 ≠ 6 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 6 t0 c76 (by decide +kernel)
  have t6 : a 29 ∈ [0] := remove (a 29) 6 [0,6] d29 b6
  have b7 : a 3 ≠ 2 := exclude [0] (edge r13) (a 3) (a 7) 2 d7 c13 (by decide +kernel)
  have t7 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk14 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,3])
    (d1 : a 1 ∈ [1])
    (d9 : a 9 ∈ [0,4])
    (d17 : a 17 ∈ [0,1])
    (d4 : a 4 ∈ [0,3])
    (d6 : a 6 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d14 : a 14 ∈ [0,3])
    (d22 : a 22 ∈ [0,1])
    (d15 : a 15 ∈ [0,13])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d11 : a 11 ∈ [0,6])
    (d27 : a 27 ∈ [0,3])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    : a 5 ∈ [3] ∧ a 9 ∈ [4] ∧ a 17 ∈ [1] ∧ a 4 ∈ [3] ∧ a 6 ∈ [1] ∧ a 12 ∈ [1] ∧ a 7 ∈ [2] ∧ a 14 ∈ [3] ∧ a 22 ∈ [1] ∧ a 15 ∈ [13] ∧ a 23 ∈ [1] ∧ a 8 ∈ [1] ∧ a 10 ∈ [1] ∧ a 24 ∈ [1] ∧ a 11 ∈ [6] ∧ a 27 ∈ [3] := by
  have b0 : a 5 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 5) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [3] := remove (a 5) 0 [0,3] d5 b0
  have b1 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [4] := remove (a 9) 0 [0,4] d9 b1
  have b2 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b2
  have b3 : a 4 ≠ 0 := exclude [3] (edge r16) (a 4) (a 5) 0 t0 c16 (by decide +kernel)
  have t3 : a 4 ∈ [3] := remove (a 4) 0 [0,3] d4 b3
  have b4 : a 6 ≠ 0 := exclude [3] (fun u v => edge r17 v u) (a 6) (a 4) 0 t3 c17 (by decide +kernel)
  have t4 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b4
  have b5 : a 12 ≠ 0 := exclude [3] (fun u v => edge r18 v u) (a 12) (a 4) 0 t3 c18 (by decide +kernel)
  have t5 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b5
  have b6 : a 7 ≠ 0 := exclude [3] (fun u v => edge r20 v u) (a 7) (a 5) 0 t0 c20 (by decide +kernel)
  have t6 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b6
  have b7 : a 14 ≠ 0 := exclude [1] (fun u v => edge r24 v u) (a 14) (a 6) 0 t4 c24 (by decide +kernel)
  have t7 : a 14 ∈ [3] := remove (a 14) 0 [0,3] d14 b7
  have b8 : a 22 ≠ 0 := exclude [1] (fun u v => edge r25 v u) (a 22) (a 6) 0 t4 c25 (by decide +kernel)
  have t8 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b8
  have b9 : a 15 ≠ 0 := exclude [2] (fun u v => edge r26 v u) (a 15) (a 7) 0 t6 c26 (by decide +kernel)
  have t9 : a 15 ∈ [13] := remove (a 15) 0 [0,13] d15 b9
  have b10 : a 23 ≠ 0 := exclude [2] (fun u v => edge r27 v u) (a 23) (a 7) 0 t6 c27 (by decide +kernel)
  have t10 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b10
  have b11 : a 8 ≠ 0 := exclude [4] (edge r28) (a 8) (a 9) 0 t1 c28 (by decide +kernel)
  have t11 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b11
  have b12 : a 10 ≠ 0 := exclude [1] (fun u v => edge r29 v u) (a 10) (a 8) 0 t11 c29 (by decide +kernel)
  have t12 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b12
  have b13 : a 24 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 24) (a 8) 0 t11 c31 (by decide +kernel)
  have t13 : a 24 ∈ [1] := remove (a 24) 0 [0,1] d24 b13
  have b14 : a 11 ≠ 0 := exclude [4] (fun u v => edge r32 v u) (a 11) (a 9) 0 t1 c32 (by decide +kernel)
  have t14 : a 11 ∈ [6] := remove (a 11) 0 [0,6] d11 b14
  have b15 : a 27 ≠ 0 := exclude [6] (fun u v => edge r39 v u) (a 27) (a 11) 0 t14 c39 (by decide +kernel)
  have t15 : a 27 ∈ [3] := remove (a 27) 0 [0,3] d27 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,3])
    (d12 : a 12 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [3])
    (d16 : a 16 ∈ [0,2])
    (d17 : a 17 ∈ [1])
    (d18 : a 18 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d31 : a 31 ∈ [0,3])
    (d27 : a 27 ∈ [3])
    (d29 : a 29 ∈ [0,6])
    (d3 : a 3 ∈ [0,2])
    (d7 : a 7 ∈ [2])
    (c13 : edge r13 (a 3) (a 7)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 28 ∈ [3] ∧ a 30 ∈ [1] ∧ a 16 ∈ [2] ∧ a 18 ∈ [2] ∧ a 19 ∈ [1] ∧ a 31 ∈ [3] ∧ a 29 ∈ [6] ∧ a 3 ∈ [2] := by
  have b0 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 d12 c42 (by decide +kernel)
  have t0 : a 28 ∈ [3] := remove (a 28) 0 [0,3] d28 b0
  have b1 : a 30 ≠ 0 := exclude [3] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b1
  have b2 : a 16 ≠ 0 := exclude [1] (edge r48) (a 16) (a 17) 0 d17 c48 (by decide +kernel)
  have t2 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b2
  have b3 : a 18 ≠ 0 := exclude [2] (fun u v => edge r49 v u) (a 18) (a 16) 0 t2 c49 (by decide +kernel)
  have t3 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b3
  have b4 : a 19 ≠ 0 := exclude [1] (fun u v => edge r52 v u) (a 19) (a 17) 0 d17 c52 (by decide +kernel)
  have t4 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b4
  have b5 : a 31 ≠ 0 := exclude [3] (fun u v => edge r75 v u) (a 31) (a 27) 0 d27 c75 (by decide +kernel)
  have t5 : a 31 ∈ [3] := remove (a 31) 0 [0,3] d31 b5
  have b6 : a 29 ≠ 0 := exclude [3] (fun u v => edge r76 v u) (a 29) (a 28) 0 t0 c76 (by decide +kernel)
  have t6 : a 29 ∈ [6] := remove (a 29) 0 [0,6] d29 b6
  have b7 : a 3 ≠ 0 := exclude [2] (edge r13) (a 3) (a 7) 0 d7 c13 (by decide +kernel)
  have t7 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_175
