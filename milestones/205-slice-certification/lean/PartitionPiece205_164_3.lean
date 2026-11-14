import PartitionData205_164
namespace PartitionCover205_164
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d6 : a 6 ∈ [0,2])
    (d20 : a 20 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,1])
    (d23 : a 23 ∈ [0,2])
    (d8 : a 8 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d11 : a 11 ∈ [0,4])
    (d26 : a 26 ∈ [0,2])
    (d16 : a 16 ∈ [0,2])
    (d18 : a 18 ∈ [0,2])
    (c6 : edge r6 (a 1) (a 5)=true)
    (c7 : edge r7 (a 1) (a 9)=true)
    (c8 : edge r8 (a 1) (a 17)=true)
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    : a 5 ∈ [1] ∧ a 9 ∈ [1] ∧ a 17 ∈ [1] ∧ a 4 ∈ [2] ∧ a 6 ∈ [2] ∧ a 20 ∈ [1] ∧ a 7 ∈ [1] ∧ a 14 ∈ [1] ∧ a 22 ∈ [1] ∧ a 23 ∈ [2] ∧ a 8 ∈ [1] ∧ a 10 ∈ [1] ∧ a 11 ∈ [4] ∧ a 26 ∈ [2] ∧ a 16 ∈ [2] ∧ a 18 ∈ [2] := by
  have b0 : a 5 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 5) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b0
  have b1 : a 9 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 9) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b1
  have b2 : a 17 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 17) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b2
  have b3 : a 4 ≠ 0 := exclude [1] (edge r16) (a 4) (a 5) 0 t0 c16 (by decide +kernel)
  have t3 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b3
  have b4 : a 6 ≠ 0 := exclude [2] (fun u v => edge r17 v u) (a 6) (a 4) 0 t3 c17 (by decide +kernel)
  have t4 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b4
  have b5 : a 20 ≠ 0 := exclude [2] (fun u v => edge r19 v u) (a 20) (a 4) 0 t3 c19 (by decide +kernel)
  have t5 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b5
  have b6 : a 7 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 7) (a 5) 0 t0 c20 (by decide +kernel)
  have t6 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b6
  have b7 : a 14 ≠ 0 := exclude [2] (fun u v => edge r24 v u) (a 14) (a 6) 0 t4 c24 (by decide +kernel)
  have t7 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b7
  have b8 : a 22 ≠ 0 := exclude [2] (fun u v => edge r25 v u) (a 22) (a 6) 0 t4 c25 (by decide +kernel)
  have t8 : a 22 ∈ [1] := remove (a 22) 0 [0,1] d22 b8
  have b9 : a 23 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 23) (a 7) 0 t6 c27 (by decide +kernel)
  have t9 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b9
  have b10 : a 8 ≠ 0 := exclude [1] (edge r28) (a 8) (a 9) 0 t1 c28 (by decide +kernel)
  have t10 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b10
  have b11 : a 10 ≠ 0 := exclude [1] (fun u v => edge r29 v u) (a 10) (a 8) 0 t10 c29 (by decide +kernel)
  have t11 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b11
  have b12 : a 11 ≠ 0 := exclude [1] (fun u v => edge r32 v u) (a 11) (a 9) 0 t1 c32 (by decide +kernel)
  have t12 : a 11 ∈ [4] := remove (a 11) 0 [0,4] d11 b12
  have b13 : a 26 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 26) (a 10) 0 t11 c37 (by decide +kernel)
  have t13 : a 26 ∈ [2] := remove (a 26) 0 [0,2] d26 b13
  have b14 : a 16 ≠ 0 := exclude [1] (edge r48) (a 16) (a 17) 0 t2 c48 (by decide +kernel)
  have t14 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b14
  have b15 : a 18 ≠ 0 := exclude [2] (fun u v => edge r49 v u) (a 18) (a 16) 0 t14 c49 (by decide +kernel)
  have t15 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk13 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,2])
    (d17 : a 17 ∈ [1])
    (d28 : a 28 ∈ [0,1])
    (d20 : a 20 ∈ [1])
    (d31 : a 31 ∈ [0,1])
    (d23 : a 23 ∈ [2])
    (d29 : a 29 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [2])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 19 ∈ [2] ∧ a 28 ∈ [1] ∧ a 31 ∈ [1] ∧ a 29 ∈ [1] ∧ a 2 ∈ [1] := by
  have b0 : a 19 ≠ 0 := exclude [1] (fun u v => edge r52 v u) (a 19) (a 17) 0 d17 c52 (by decide +kernel)
  have t0 : a 19 ∈ [2] := remove (a 19) 0 [0,2] d19 b0
  have b1 : a 28 ≠ 0 := exclude [1] (fun u v => edge r62 v u) (a 28) (a 20) 0 d20 c62 (by decide +kernel)
  have t1 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b1
  have b2 : a 31 ≠ 0 := exclude [2] (fun u v => edge r67 v u) (a 31) (a 23) 0 d23 c67 (by decide +kernel)
  have t2 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b2
  have b3 : a 29 ≠ 0 := exclude [1] (fun u v => edge r76 v u) (a 29) (a 28) 0 t1 c76 (by decide +kernel)
  have t3 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b3
  have b4 : a 2 ≠ 0 := exclude [2] (edge r10) (a 2) (a 6) 0 d6 c10 (by decide +kernel)
  have t4 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))
#print axioms chunk12
#print axioms chunk13
end PartitionCover205_164
