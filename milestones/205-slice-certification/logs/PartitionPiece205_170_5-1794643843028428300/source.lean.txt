import PartitionData205_170
namespace PartitionCover205_170
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk20 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1,5,8,16,18])
    (d21 : a 21 ∈ [0])
    (d30 : a 30 ∈ [0,1,8,9,13,17])
    (d22 : a 22 ∈ [0])
    (d31 : a 31 ∈ [0,1,9])
    (d23 : a 23 ∈ [0])
    (d24 : a 24 ∈ [0,3,10])
    (d25 : a 25 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d27 : a 27 ∈ [0,2])
    (d28 : a 28 ∈ [0])
    (c64 : edge r64 (a 21) (a 29)=true)
    (c66 : edge r66 (a 22) (a 30)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c69 : edge r69 (a 24) (a 26)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    (c75 : edge r75 (a 27) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 24 ∈ [0] ∧ a 25 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 29 ≠ 16 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 16 d21 c64 (by decide +kernel)
  have t0 : a 29 ∈ [0,1,5,8,18] := remove (a 29) 16 [0,1,5,8,16,18] d29 b0
  have b1 : a 29 ≠ 18 := exclude [0] (fun u v => edge r64 v u) (a 29) (a 21) 18 d21 c64 (by decide +kernel)
  have t1 : a 29 ∈ [0,1,5,8] := remove (a 29) 18 [0,1,5,8,18] t0 b1
  have b2 : a 30 ≠ 1 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 1 d22 c66 (by decide +kernel)
  have t2 : a 30 ∈ [0,8,9,13,17] := remove (a 30) 1 [0,1,8,9,13,17] d30 b2
  have b3 : a 30 ≠ 9 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 9 d22 c66 (by decide +kernel)
  have t3 : a 30 ∈ [0,8,13,17] := remove (a 30) 9 [0,8,9,13,17] t2 b3
  have b4 : a 30 ≠ 13 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 13 d22 c66 (by decide +kernel)
  have t4 : a 30 ∈ [0,8,17] := remove (a 30) 13 [0,8,13,17] t3 b4
  have b5 : a 30 ≠ 17 := exclude [0] (fun u v => edge r66 v u) (a 30) (a 22) 17 d22 c66 (by decide +kernel)
  have t5 : a 30 ∈ [0,8] := remove (a 30) 17 [0,8,17] t4 b5
  have b6 : a 31 ≠ 9 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 9 d23 c67 (by decide +kernel)
  have t6 : a 31 ∈ [0,1] := remove (a 31) 9 [0,1,9] d31 b6
  have b7 : a 24 ≠ 3 := exclude [0,1] (edge r68) (a 24) (a 25) 3 d25 c68 (by decide +kernel)
  have t7 : a 24 ∈ [0,10] := remove (a 24) 3 [0,3,10] d24 b7
  have b8 : a 24 ≠ 10 := exclude [0] (edge r69) (a 24) (a 26) 10 d26 c69 (by decide +kernel)
  have t8 : a 24 ∈ [0] := remove (a 24) 10 [0,10] t7 b8
  have b9 : a 25 ≠ 1 := exclude [0,1,5,8] (edge r72) (a 25) (a 29) 1 t1 c72 (by decide +kernel)
  have t9 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b9
  have b10 : a 29 ≠ 5 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 5 t9 c72 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,8] := remove (a 29) 5 [0,1,5,8] t1 b10
  have b11 : a 29 ≠ 8 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 25) 8 t9 c72 (by decide +kernel)
  have t11 : a 29 ∈ [0,1] := remove (a 29) 8 [0,1,8] t10 b11
  have b12 : a 27 ≠ 2 := exclude [0] (fun u v => edge r73 v u) (a 27) (a 26) 2 d26 c73 (by decide +kernel)
  have t12 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b12
  have b13 : a 30 ≠ 8 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 8 d26 c74 (by decide +kernel)
  have t13 : a 30 ∈ [0] := remove (a 30) 8 [0,8] t5 b13
  have b14 : a 31 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 31) (a 27) 1 t12 c75 (by decide +kernel)
  have t14 : a 31 ∈ [0] := remove (a 31) 1 [0,1] t6 b14
  have b15 : a 29 ≠ 1 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 1 d28 c76 (by decide +kernel)
  have t15 : a 29 ∈ [0] := remove (a 29) 1 [0,1] t11 b15
  exact And.intro t15 (And.intro t13 (And.intro t14 (And.intro t8 (And.intro t9 (t12)))))

theorem chunk21 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [0,2])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    : a 2 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0] := by
  have b0 : a 2 ≠ 1 := exclude [0] (edge r10) (a 2) (a 6) 1 d6 c10 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 9 ≠ 1 := exclude [0] (edge r34) (a 9) (a 25) 1 d25 c34 (by decide +kernel)
  have t1 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b1
  have b2 : a 17 ≠ 1 := exclude [0] (edge r52) (a 17) (a 19) 1 d19 c52 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b2
  have b3 : a 16 ≠ 1 := exclude [0] (edge r48) (a 16) (a 17) 1 t2 c48 (by decide +kernel)
  have t3 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b3
  have b4 : a 18 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 18) (a 16) 2 t3 c49 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 2 [0,2] d18 b4
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t4))))
#print axioms chunk20
#print axioms chunk21
end PartitionCover205_170
