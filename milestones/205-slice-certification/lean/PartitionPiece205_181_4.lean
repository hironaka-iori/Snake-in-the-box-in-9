import PartitionData205_181
namespace PartitionCover205_181
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk16 (a : Nat → Nat)
    (d9 : a 9 ∈ [0,3])
    (d1 : a 1 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d8 : a 8 ∈ [0,6])
    (d10 : a 10 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d24 : a 24 ∈ [0,6])
    (d11 : a 11 ∈ [0,6])
    (d14 : a 14 ∈ [0,4])
    (d26 : a 26 ∈ [0,3])
    (d15 : a 15 ∈ [0,12])
    (d30 : a 30 ∈ [0,6])
    (d31 : a 31 ∈ [0,2])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d19 : a 19 ∈ [0,1])
    (d23 : a 23 ∈ [0,6])
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    : a 9 ∈ [3] ∧ a 17 ∈ [1] ∧ a 8 ∈ [6] ∧ a 10 ∈ [1] ∧ a 12 ∈ [2] ∧ a 24 ∈ [6] ∧ a 11 ∈ [6] ∧ a 14 ∈ [4] ∧ a 26 ∈ [3] ∧ a 15 ∈ [12] ∧ a 30 ∈ [6] ∧ a 31 ∈ [2] ∧ a 16 ∈ [1] ∧ a 18 ∈ [1] ∧ a 19 ∈ [1] ∧ a 23 ∈ [6] := by
  have b0 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t0 : a 9 ∈ [3] := remove (a 9) 0 [0,3] d9 b0
  have b1 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t1 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b1
  have b2 : a 8 ≠ 0 := exclude [3] (edge r28) (a 8) (a 9) 0 t0 c28 (by decide +kernel)
  have t2 : a 8 ∈ [6] := remove (a 8) 0 [0,6] d8 b2
  have b3 : a 10 ≠ 0 := exclude [6] (fun u v => edge r29 v u) (a 10) (a 8) 0 t2 c29 (by decide +kernel)
  have t3 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b3
  have b4 : a 12 ≠ 0 := exclude [6] (fun u v => edge r30 v u) (a 12) (a 8) 0 t2 c30 (by decide +kernel)
  have t4 : a 12 ∈ [2] := remove (a 12) 0 [0,2] d12 b4
  have b5 : a 24 ≠ 0 := exclude [6] (fun u v => edge r31 v u) (a 24) (a 8) 0 t2 c31 (by decide +kernel)
  have t5 : a 24 ∈ [6] := remove (a 24) 0 [0,6] d24 b5
  have b6 : a 11 ≠ 0 := exclude [3] (fun u v => edge r32 v u) (a 11) (a 9) 0 t0 c32 (by decide +kernel)
  have t6 : a 11 ∈ [6] := remove (a 11) 0 [0,6] d11 b6
  have b7 : a 14 ≠ 0 := exclude [1] (fun u v => edge r36 v u) (a 14) (a 10) 0 t3 c36 (by decide +kernel)
  have t7 : a 14 ∈ [4] := remove (a 14) 0 [0,4] d14 b7
  have b8 : a 26 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 26) (a 10) 0 t3 c37 (by decide +kernel)
  have t8 : a 26 ∈ [3] := remove (a 26) 0 [0,3] d26 b8
  have b9 : a 15 ≠ 0 := exclude [6] (fun u v => edge r38 v u) (a 15) (a 11) 0 t6 c38 (by decide +kernel)
  have t9 : a 15 ∈ [12] := remove (a 15) 0 [0,12] d15 b9
  have b10 : a 30 ≠ 0 := exclude [4] (fun u v => edge r46 v u) (a 30) (a 14) 0 t7 c46 (by decide +kernel)
  have t10 : a 30 ∈ [6] := remove (a 30) 0 [0,6] d30 b10
  have b11 : a 31 ≠ 0 := exclude [12] (fun u v => edge r47 v u) (a 31) (a 15) 0 t9 c47 (by decide +kernel)
  have t11 : a 31 ∈ [2] := remove (a 31) 0 [0,2] d31 b11
  have b12 : a 16 ≠ 0 := exclude [1] (edge r48) (a 16) (a 17) 0 t1 c48 (by decide +kernel)
  have t12 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b12
  have b13 : a 18 ≠ 0 := exclude [1] (fun u v => edge r49 v u) (a 18) (a 16) 0 t12 c49 (by decide +kernel)
  have t13 : a 18 ∈ [1] := remove (a 18) 0 [0,1] d18 b13
  have b14 : a 19 ≠ 0 := exclude [1] (fun u v => edge r52 v u) (a 19) (a 17) 0 t1 c52 (by decide +kernel)
  have t14 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b14
  have b15 : a 23 ≠ 0 := exclude [1] (fun u v => edge r58 v u) (a 23) (a 19) 0 t14 c58 (by decide +kernel)
  have t15 : a 23 ∈ [6] := remove (a 23) 0 [0,6] d23 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk17 (a : Nat → Nat)
    (d28 : a 28 ∈ [0,1])
    (d30 : a 30 ∈ [6])
    (d29 : a 29 ∈ [0,2])
    (d31 : a 31 ∈ [2])
    (d3 : a 3 ∈ [0,1])
    (d11 : a 11 ∈ [6])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [2])
    (d20 : a 20 ∈ [0,2])
    (d6 : a 6 ∈ [0,1])
    (d14 : a 14 ∈ [4])
    (d7 : a 7 ∈ [0,3])
    (d15 : a 15 ∈ [12])
    (d5 : a 5 ∈ [0,2])
    (c14 : edge r14 (a 3) (a 11)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    (c78 : edge r78 (a 29) (a 31)=true)
    : a 28 ∈ [1] ∧ a 29 ∈ [2] ∧ a 3 ∈ [1] ∧ a 4 ∈ [1] ∧ a 20 ∈ [2] ∧ a 6 ∈ [1] ∧ a 7 ∈ [3] ∧ a 5 ∈ [2] := by
  have b0 : a 28 ≠ 0 := exclude [6] (edge r77) (a 28) (a 30) 0 d30 c77 (by decide +kernel)
  have t0 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b0
  have b1 : a 29 ≠ 0 := exclude [2] (edge r78) (a 29) (a 31) 0 d31 c78 (by decide +kernel)
  have t1 : a 29 ∈ [2] := remove (a 29) 0 [0,2] d29 b1
  have b2 : a 3 ≠ 0 := exclude [6] (edge r14) (a 3) (a 11) 0 d11 c14 (by decide +kernel)
  have t2 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b2
  have b3 : a 4 ≠ 0 := exclude [2] (edge r18) (a 4) (a 12) 0 d12 c18 (by decide +kernel)
  have t3 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b3
  have b4 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t3 c19 (by decide +kernel)
  have t4 : a 20 ∈ [2] := remove (a 20) 0 [0,2] d20 b4
  have b5 : a 6 ≠ 0 := exclude [4] (edge r24) (a 6) (a 14) 0 d14 c24 (by decide +kernel)
  have t5 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b5
  have b6 : a 7 ≠ 0 := exclude [12] (edge r26) (a 7) (a 15) 0 d15 c26 (by decide +kernel)
  have t6 : a 7 ∈ [3] := remove (a 7) 0 [0,3] d7 b6
  have b7 : a 5 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 5) (a 4) 0 t3 c16 (by decide +kernel)
  have t7 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk16
#print axioms chunk17
end PartitionCover205_181
