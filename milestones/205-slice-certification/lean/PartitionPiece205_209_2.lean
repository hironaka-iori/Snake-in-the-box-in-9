import PartitionData205_209
namespace PartitionCover205_209
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,2])
    (d1 : a 1 ∈ [1])
    (d2 : a 2 ∈ [0,2])
    (d6 : a 6 ∈ [0,2])
    (d7 : a 7 ∈ [0,2])
    (d5 : a 5 ∈ [0,2])
    (d21 : a 21 ∈ [0,2])
    (d22 : a 22 ∈ [0,3])
    (d15 : a 15 ∈ [0,2])
    (d23 : a 23 ∈ [0,6])
    (d11 : a 11 ∈ [0,2])
    (d31 : a 31 ∈ [0,3])
    (d17 : a 17 ∈ [0,2])
    (d29 : a 29 ∈ [0,2])
    (d30 : a 30 ∈ [0,3])
    (d25 : a 25 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c22 : edge r22 (a 5) (a 21)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 3 ∈ [2] ∧ a 2 ∈ [2] ∧ a 6 ∈ [2] ∧ a 7 ∈ [2] ∧ a 5 ∈ [2] ∧ a 21 ∈ [2] ∧ a 22 ∈ [3] ∧ a 15 ∈ [2] ∧ a 23 ∈ [6] ∧ a 11 ∈ [2] ∧ a 31 ∈ [3] ∧ a 17 ∈ [2] ∧ a 29 ∈ [2] ∧ a 30 ∈ [3] ∧ a 25 ∈ [1] ∧ a 26 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b0
  have b1 : a 2 ≠ 0 := exclude [2] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [2] := remove (a 2) 0 [0,2] d2 b1
  have b2 : a 6 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 6) (a 2) 0 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b2
  have b3 : a 7 ≠ 0 := exclude [2] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b3
  have b4 : a 5 ≠ 0 := exclude [2] (edge r20) (a 5) (a 7) 0 t3 c20 (by decide +kernel)
  have t4 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b4
  have b5 : a 21 ≠ 0 := exclude [2] (fun u v => edge r22 v u) (a 21) (a 5) 0 t4 c22 (by decide +kernel)
  have t5 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b5
  have b6 : a 22 ≠ 0 := exclude [2] (fun u v => edge r25 v u) (a 22) (a 6) 0 t2 c25 (by decide +kernel)
  have t6 : a 22 ∈ [3] := remove (a 22) 0 [0,3] d22 b6
  have b7 : a 15 ≠ 0 := exclude [2] (fun u v => edge r26 v u) (a 15) (a 7) 0 t3 c26 (by decide +kernel)
  have t7 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b7
  have b8 : a 23 ≠ 0 := exclude [2] (fun u v => edge r27 v u) (a 23) (a 7) 0 t3 c27 (by decide +kernel)
  have t8 : a 23 ∈ [6] := remove (a 23) 0 [0,6] d23 b8
  have b9 : a 11 ≠ 0 := exclude [2] (edge r38) (a 11) (a 15) 0 t7 c38 (by decide +kernel)
  have t9 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b9
  have b10 : a 31 ≠ 0 := exclude [2] (fun u v => edge r47 v u) (a 31) (a 15) 0 t7 c47 (by decide +kernel)
  have t10 : a 31 ∈ [3] := remove (a 31) 0 [0,3] d31 b10
  have b11 : a 17 ≠ 0 := exclude [2] (edge r53) (a 17) (a 21) 0 t5 c53 (by decide +kernel)
  have t11 : a 17 ∈ [2] := remove (a 17) 0 [0,2] d17 b11
  have b12 : a 29 ≠ 0 := exclude [2] (fun u v => edge r64 v u) (a 29) (a 21) 0 t5 c64 (by decide +kernel)
  have t12 : a 29 ∈ [2] := remove (a 29) 0 [0,2] d29 b12
  have b13 : a 30 ≠ 0 := exclude [3] (fun u v => edge r66 v u) (a 30) (a 22) 0 t6 c66 (by decide +kernel)
  have t13 : a 30 ∈ [3] := remove (a 30) 0 [0,3] d30 b13
  have b14 : a 25 ≠ 0 := exclude [2] (edge r72) (a 25) (a 29) 0 t12 c72 (by decide +kernel)
  have t14 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b14
  have b15 : a 26 ≠ 0 := exclude [3] (edge r74) (a 26) (a 30) 0 t13 c74 (by decide +kernel)
  have t15 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d27 : a 27 ∈ [0,1])
    (d31 : a 31 ∈ [3])
    (d28 : a 28 ∈ [0,4])
    (d29 : a 29 ∈ [2])
    (d9 : a 9 ∈ [0,2])
    (d11 : a 11 ∈ [2])
    (d16 : a 16 ∈ [0,1])
    (d17 : a 17 ∈ [2])
    (d20 : a 20 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (c19 : edge r19 (a 4) (a 20)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 27 ∈ [1] ∧ a 28 ∈ [4] ∧ a 9 ∈ [2] ∧ a 16 ∈ [1] ∧ a 20 ∈ [1] ∧ a 4 ∈ [1] ∧ a 8 ∈ [1] ∧ a 12 ∈ [1] := by
  have b0 : a 27 ≠ 0 := exclude [3] (edge r75) (a 27) (a 31) 0 d31 c75 (by decide +kernel)
  have t0 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b0
  have b1 : a 28 ≠ 0 := exclude [2] (edge r76) (a 28) (a 29) 0 d29 c76 (by decide +kernel)
  have t1 : a 28 ∈ [4] := remove (a 28) 0 [0,4] d28 b1
  have b2 : a 9 ≠ 0 := exclude [2] (edge r32) (a 9) (a 11) 0 d11 c32 (by decide +kernel)
  have t2 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b2
  have b3 : a 16 ≠ 0 := exclude [2] (edge r48) (a 16) (a 17) 0 d17 c48 (by decide +kernel)
  have t3 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b3
  have b4 : a 20 ≠ 0 := exclude [1] (fun u v => edge r50 v u) (a 20) (a 16) 0 t3 c50 (by decide +kernel)
  have t4 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b4
  have b5 : a 4 ≠ 0 := exclude [1] (edge r19) (a 4) (a 20) 0 t4 c19 (by decide +kernel)
  have t5 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b5
  have b6 : a 8 ≠ 0 := exclude [2] (edge r28) (a 8) (a 9) 0 t2 c28 (by decide +kernel)
  have t6 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b6
  have b7 : a 12 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 12) (a 8) 0 t6 c30 (by decide +kernel)
  have t7 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_209
