import PartitionData205_179
namespace PartitionCover205_179
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1,3,4,5,6,7,8,9,10,11])
    (d27 : a 27 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d31 : a 31 ∈ [0])
    (d28 : a 28 ∈ [0,2])
    (d30 : a 30 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (c22 : edge r22 (a 5) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c77 : edge r77 (a 28) (a 30)=true)
    : a 25 ∈ [0,1] ∧ a 29 ∈ [0,1] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 5 ∈ [0] := by
  have b0 : a 25 ≠ 3 := exclude [0,1] (edge r71) (a 25) (a 27) 3 d27 c71 (by decide +kernel)
  have t0 : a 25 ∈ [0,1,4,5,6,7,8,9,10,11] := remove (a 25) 3 [0,1,3,4,5,6,7,8,9,10,11] d25 b0
  have b1 : a 25 ≠ 4 := exclude [0,1] (edge r71) (a 25) (a 27) 4 d27 c71 (by decide +kernel)
  have t1 : a 25 ∈ [0,1,5,6,7,8,9,10,11] := remove (a 25) 4 [0,1,4,5,6,7,8,9,10,11] t0 b1
  have b2 : a 25 ≠ 5 := exclude [0,1] (edge r71) (a 25) (a 27) 5 d27 c71 (by decide +kernel)
  have t2 : a 25 ∈ [0,1,6,7,8,9,10,11] := remove (a 25) 5 [0,1,5,6,7,8,9,10,11] t1 b2
  have b3 : a 25 ≠ 6 := exclude [0,1] (edge r71) (a 25) (a 27) 6 d27 c71 (by decide +kernel)
  have t3 : a 25 ∈ [0,1,7,8,9,10,11] := remove (a 25) 6 [0,1,6,7,8,9,10,11] t2 b3
  have b4 : a 25 ≠ 7 := exclude [0,1] (edge r71) (a 25) (a 27) 7 d27 c71 (by decide +kernel)
  have t4 : a 25 ∈ [0,1,8,9,10,11] := remove (a 25) 7 [0,1,7,8,9,10,11] t3 b4
  have b5 : a 25 ≠ 8 := exclude [0,1] (edge r71) (a 25) (a 27) 8 d27 c71 (by decide +kernel)
  have t5 : a 25 ∈ [0,1,9,10,11] := remove (a 25) 8 [0,1,8,9,10,11] t4 b5
  have b6 : a 25 ≠ 9 := exclude [0,1] (edge r71) (a 25) (a 27) 9 d27 c71 (by decide +kernel)
  have t6 : a 25 ∈ [0,1,10,11] := remove (a 25) 9 [0,1,9,10,11] t5 b6
  have b7 : a 25 ≠ 10 := exclude [0,1,2,3,4,5] (edge r72) (a 25) (a 29) 10 d29 c72 (by decide +kernel)
  have t7 : a 25 ∈ [0,1,11] := remove (a 25) 10 [0,1,10,11] t6 b7
  have b8 : a 25 ≠ 11 := exclude [0,1,2,3,4,5] (edge r72) (a 25) (a 29) 11 d29 c72 (by decide +kernel)
  have t8 : a 25 ∈ [0,1] := remove (a 25) 11 [0,1,11] t7 b8
  have b9 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r72 v u) (a 29) (a 25) 2 t8 c72 (by decide +kernel)
  have t9 : a 29 ∈ [0,1,3,4,5] := remove (a 29) 2 [0,1,2,3,4,5] d29 b9
  have b10 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r72 v u) (a 29) (a 25) 3 t8 c72 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,4,5] := remove (a 29) 3 [0,1,3,4,5] t9 b10
  have b11 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r72 v u) (a 29) (a 25) 4 t8 c72 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,5] := remove (a 29) 4 [0,1,4,5] t10 b11
  have b12 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r72 v u) (a 29) (a 25) 5 t8 c72 (by decide +kernel)
  have t12 : a 29 ∈ [0,1] := remove (a 29) 5 [0,1,5] t11 b12
  have b13 : a 27 ≠ 1 := exclude [0] (edge r75) (a 27) (a 31) 1 d31 c75 (by decide +kernel)
  have t13 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b13
  have b14 : a 28 ≠ 2 := exclude [0] (edge r77) (a 28) (a 30) 2 d30 c77 (by decide +kernel)
  have t14 : a 28 ∈ [0] := remove (a 28) 2 [0,2] d28 b14
  have b15 : a 5 ≠ 1 := exclude [0,1] (edge r22) (a 5) (a 21) 1 d21 c22 (by decide +kernel)
  have t15 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b15
  exact And.intro t8 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))

theorem chunk13 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2])
    (d15 : a 15 ∈ [0])
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d16 : a 16 ∈ [0,1,14,15])
    (d17 : a 17 ∈ [0,1,2,3,4,5,8,9,10,11])
    (d21 : a 21 ∈ [0,1])
    (d23 : a 23 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c63 : edge r63 (a 21) (a 23)=true)
    (c70 : edge r70 (a 24) (a 28)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 7 ∈ [0] ∧ a 8 ∈ [0] ∧ a 16 ∈ [0,1] ∧ a 17 ∈ [0,1] ∧ a 21 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 29 ∈ [0] := by
  have b0 : a 7 ≠ 2 := exclude [0] (edge r26) (a 7) (a 15) 2 d15 c26 (by decide +kernel)
  have t0 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b0
  have b1 : a 8 ≠ 1 := exclude [0] (edge r28) (a 8) (a 9) 1 d9 c28 (by decide +kernel)
  have t1 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b1
  have b2 : a 16 ≠ 14 := exclude [0,1,2,3,4,5,8,9,10,11] (edge r48) (a 16) (a 17) 14 d17 c48 (by decide +kernel)
  have t2 : a 16 ∈ [0,1,15] := remove (a 16) 14 [0,1,14,15] d16 b2
  have b3 : a 16 ≠ 15 := exclude [0,1,2,3,4,5,8,9,10,11] (edge r48) (a 16) (a 17) 15 d17 c48 (by decide +kernel)
  have t3 : a 16 ∈ [0,1] := remove (a 16) 15 [0,1,15] t2 b3
  have b4 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 2 t3 c48 (by decide +kernel)
  have t4 : a 17 ∈ [0,1,3,4,5,8,9,10,11] := remove (a 17) 2 [0,1,2,3,4,5,8,9,10,11] d17 b4
  have b5 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 3 t3 c48 (by decide +kernel)
  have t5 : a 17 ∈ [0,1,4,5,8,9,10,11] := remove (a 17) 3 [0,1,3,4,5,8,9,10,11] t4 b5
  have b6 : a 17 ≠ 4 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 4 t3 c48 (by decide +kernel)
  have t6 : a 17 ∈ [0,1,5,8,9,10,11] := remove (a 17) 4 [0,1,4,5,8,9,10,11] t5 b6
  have b7 : a 17 ≠ 5 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 5 t3 c48 (by decide +kernel)
  have t7 : a 17 ∈ [0,1,8,9,10,11] := remove (a 17) 5 [0,1,5,8,9,10,11] t6 b7
  have b8 : a 17 ≠ 8 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 8 t3 c48 (by decide +kernel)
  have t8 : a 17 ∈ [0,1,9,10,11] := remove (a 17) 8 [0,1,8,9,10,11] t7 b8
  have b9 : a 17 ≠ 9 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 9 t3 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0,1,10,11] := remove (a 17) 9 [0,1,9,10,11] t8 b9
  have b10 : a 17 ≠ 10 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 10 t3 c48 (by decide +kernel)
  have t10 : a 17 ∈ [0,1,11] := remove (a 17) 10 [0,1,10,11] t9 b10
  have b11 : a 17 ≠ 11 := exclude [0,1] (fun u v => edge r48 v u) (a 17) (a 16) 11 t3 c48 (by decide +kernel)
  have t11 : a 17 ∈ [0,1] := remove (a 17) 11 [0,1,11] t10 b11
  have b12 : a 21 ≠ 1 := exclude [0] (edge r63) (a 21) (a 23) 1 d23 c63 (by decide +kernel)
  have t12 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b12
  have b13 : a 24 ≠ 1 := exclude [0] (edge r70) (a 24) (a 28) 1 d28 c70 (by decide +kernel)
  have t13 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b13
  have b14 : a 25 ≠ 1 := exclude [0] (edge r71) (a 25) (a 27) 1 d27 c71 (by decide +kernel)
  have t14 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b14
  have b15 : a 29 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 1 t14 c72 (by decide +kernel)
  have t15 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))

theorem chunk14 (a : Nat → Nat)
    (d17 : a 17 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    : a 17 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] := by
  have b0 : a 17 ≠ 1 := exclude [0] (edge r53) (a 17) (a 21) 1 d21 c53 (by decide +kernel)
  have t0 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b0
  have b1 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 17) 1 t0 c48 (by decide +kernel)
  have t1 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b1
  have b2 : a 18 ≠ 1 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 1 t1 c49 (by decide +kernel)
  have t2 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b2
  exact And.intro t0 (And.intro t1 (t2))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
end PartitionCover205_179
