import PartitionData205_166
namespace PartitionCover205_166
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,6,9])
    (d16 : a 16 ∈ [0,6])
    (d19 : a 19 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d18 : a 18 ∈ [0,6])
    (d22 : a 22 ∈ [0,3])
    (d23 : a 23 ∈ [0,1,6,7])
    (d20 : a 20 ∈ [0,1,6,7])
    (d28 : a 28 ∈ [0,6])
    (d21 : a 21 ∈ [0,1,6,7])
    (d29 : a 29 ∈ [0,1])
    (d24 : a 24 ∈ [0,3])
    (d6 : a 6 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c61 : edge r61 (a 20) (a 22)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c64 : edge r64 (a 21) (a 29)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    : a 17 ∈ [0] ∧ a 25 ∈ [0] ∧ a 18 ∈ [0] ∧ a 22 ∈ [0] ∧ a 23 ∈ [0,1] ∧ a 20 ∈ [0] ∧ a 28 ∈ [0] ∧ a 21 ∈ [0,1] ∧ a 29 ∈ [0] ∧ a 24 ∈ [0] ∧ a 6 ∈ [0] := by
  have b0 : a 17 ≠ 9 := exclude [0,6] (fun u v => edge r48 v u) (a 17) (a 16) 9 d16 c48 (by decide +kernel)
  have t0 : a 17 ∈ [0,6] := remove (a 17) 9 [0,6,9] d17 b0
  have b1 : a 17 ≠ 6 := exclude [0] (edge r52) (a 17) (a 19) 6 d19 c52 (by decide +kernel)
  have t1 : a 17 ∈ [0] := remove (a 17) 6 [0,6] t0 b1
  have b2 : a 25 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 25) (a 17) 1 t1 c54 (by decide +kernel)
  have t2 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b2
  have b3 : a 18 ≠ 6 := exclude [0] (edge r55) (a 18) (a 19) 6 d19 c55 (by decide +kernel)
  have t3 : a 18 ∈ [0] := remove (a 18) 6 [0,6] d18 b3
  have b4 : a 22 ≠ 3 := exclude [0] (fun u v => edge r56 v u) (a 22) (a 18) 3 t3 c56 (by decide +kernel)
  have t4 : a 22 ∈ [0] := remove (a 22) 3 [0,3] d22 b4
  have b5 : a 23 ≠ 6 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 6 d19 c58 (by decide +kernel)
  have t5 : a 23 ∈ [0,1,7] := remove (a 23) 6 [0,1,6,7] d23 b5
  have b6 : a 23 ≠ 7 := exclude [0] (fun u v => edge r58 v u) (a 23) (a 19) 7 d19 c58 (by decide +kernel)
  have t6 : a 23 ∈ [0,1] := remove (a 23) 7 [0,1,7] t5 b6
  have b7 : a 20 ≠ 6 := exclude [0] (edge r61) (a 20) (a 22) 6 t4 c61 (by decide +kernel)
  have t7 : a 20 ∈ [0,1,7] := remove (a 20) 6 [0,1,6,7] d20 b7
  have b8 : a 20 ≠ 7 := exclude [0] (edge r61) (a 20) (a 22) 7 t4 c61 (by decide +kernel)
  have t8 : a 20 ∈ [0,1] := remove (a 20) 7 [0,1,7] t7 b8
  have b9 : a 20 ≠ 1 := exclude [0,6] (edge r62) (a 20) (a 28) 1 d28 c62 (by decide +kernel)
  have t9 : a 20 ∈ [0] := remove (a 20) 1 [0,1] t8 b9
  have b10 : a 28 ≠ 6 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 6 t9 c62 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 6 [0,6] d28 b10
  have b11 : a 21 ≠ 6 := exclude [0,1] (edge r63) (a 21) (a 23) 6 t6 c63 (by decide +kernel)
  have t11 : a 21 ∈ [0,1,7] := remove (a 21) 6 [0,1,6,7] d21 b11
  have b12 : a 21 ≠ 7 := exclude [0,1] (edge r63) (a 21) (a 23) 7 t6 c63 (by decide +kernel)
  have t12 : a 21 ∈ [0,1] := remove (a 21) 7 [0,1,7] t11 b12
  have b13 : a 29 ≠ 1 := exclude [0,1] (fun u v => edge r64 v u) (a 29) (a 21) 1 t12 c64 (by decide +kernel)
  have t13 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b13
  have b14 : a 24 ≠ 3 := exclude [0] (edge r68) (a 24) (a 25) 3 t2 c68 (by decide +kernel)
  have t14 : a 24 ∈ [0] := remove (a 24) 3 [0,3] d24 b14
  have b15 : a 6 ≠ 2 := exclude [0] (edge r24) (a 6) (a 14) 2 d14 c24 (by decide +kernel)
  have t15 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b15
  exact And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))))

theorem chunk13 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d10 : a 10 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (d16 : a 16 ∈ [0,6])
    (d17 : a 17 ∈ [0])
    (d21 : a 21 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d31 : a 31 ∈ [0,2])
    (d4 : a 4 ∈ [0,2])
    (d6 : a 6 ∈ [0])
    (d5 : a 5 ∈ [0,2])
    (d13 : a 13 ∈ [0,4])
    (c17 : edge r17 (a 4) (a 6)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c41 : edge r41 (a 12) (a 14)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    : a 7 ∈ [0] ∧ a 8 ∈ [0] ∧ a 10 ∈ [0] ∧ a 12 ∈ [0] ∧ a 16 ∈ [0] ∧ a 21 ∈ [0] ∧ a 23 ∈ [0] ∧ a 31 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 7 ≠ 1 := exclude [0,1] (edge r27) (a 7) (a 23) 1 d23 c27 (by decide +kernel)
  have t0 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b0
  have b1 : a 8 ≠ 1 := exclude [0] (edge r31) (a 8) (a 24) 1 d24 c31 (by decide +kernel)
  have t1 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b1
  have b2 : a 10 ≠ 2 := exclude [0] (edge r36) (a 10) (a 14) 2 d14 c36 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b2
  have b3 : a 12 ≠ 1 := exclude [0] (edge r41) (a 12) (a 14) 1 d14 c41 (by decide +kernel)
  have t3 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b3
  have b4 : a 16 ≠ 6 := exclude [0] (edge r48) (a 16) (a 17) 6 d17 c48 (by decide +kernel)
  have t4 : a 16 ∈ [0] := remove (a 16) 6 [0,6] d16 b4
  have b5 : a 21 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 1 d20 c60 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b5
  have b6 : a 23 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 23) (a 21) 1 t5 c63 (by decide +kernel)
  have t6 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b6
  have b7 : a 31 ≠ 2 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 2 t6 c67 (by decide +kernel)
  have t7 : a 31 ∈ [0] := remove (a 31) 2 [0,2] d31 b7
  have b8 : a 4 ≠ 2 := exclude [0] (edge r17) (a 4) (a 6) 2 d6 c17 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b8
  have b9 : a 5 ≠ 2 := exclude [0] (edge r20) (a 5) (a 7) 2 t0 c20 (by decide +kernel)
  have t9 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b9
  have b10 : a 13 ≠ 4 := exclude [0] (fun u v => edge r21 v u) (a 13) (a 5) 4 t9 c21 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 4 [0,4] d13 b10
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (t10))))))))))
#print axioms chunk12
#print axioms chunk13
end PartitionCover205_166
