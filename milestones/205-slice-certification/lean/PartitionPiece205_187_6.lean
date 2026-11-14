import PartitionData205_187
namespace PartitionCover205_187
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,10])
    (d9 : a 9 ∈ [2])
    (d26 : a 26 ∈ [0,5])
    (d10 : a 10 ∈ [2])
    (d15 : a 15 ∈ [0,1])
    (d11 : a 11 ∈ [6])
    (d27 : a 27 ∈ [0,8])
    (d13 : a 13 ∈ [0,4])
    (d12 : a 12 ∈ [2])
    (d28 : a 28 ∈ [0,4])
    (d30 : a 30 ∈ [0,2])
    (d14 : a 14 ∈ [2])
    (d31 : a 31 ∈ [0,5])
    (d16 : a 16 ∈ [0,1])
    (d17 : a 17 ∈ [3])
    (d18 : a 18 ∈ [0,12])
    (d19 : a 19 ∈ [6])
    (d23 : a 23 ∈ [0,9])
    (d21 : a 21 ∈ [0,18])
    (d20 : a 20 ∈ [9])
    (d29 : a 29 ∈ [0,10])
    (d2 : a 2 ∈ [0,8])
    (d6 : a 6 ∈ [8])
    (c10 : edge r10 (a 2) (a 6)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c40 : edge r40 (a 12) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c55 : edge r55 (a 18) (a 19)=true)
    (c58 : edge r58 (a 19) (a 23)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 25 ∈ [10] ∧ a 26 ∈ [5] ∧ a 15 ∈ [1] ∧ a 27 ∈ [8] ∧ a 13 ∈ [4] ∧ a 28 ∈ [4] ∧ a 30 ∈ [2] ∧ a 31 ∈ [5] ∧ a 16 ∈ [1] ∧ a 18 ∈ [12] ∧ a 23 ∈ [9] ∧ a 21 ∈ [18] ∧ a 29 ∈ [10] ∧ a 2 ∈ [8] := by
  have b0 : a 25 ≠ 0 := exclude [2] (fun u v => edge r34 v u) (a 25) (a 9) 0 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [10] := remove (a 25) 0 [0,10] d25 b0
  have b1 : a 26 ≠ 0 := exclude [2] (fun u v => edge r37 v u) (a 26) (a 10) 0 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [5] := remove (a 26) 0 [0,5] d26 b1
  have b2 : a 15 ≠ 0 := exclude [6] (fun u v => edge r38 v u) (a 15) (a 11) 0 d11 c38 (by decide +kernel)
  have t2 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b2
  have b3 : a 27 ≠ 0 := exclude [6] (fun u v => edge r39 v u) (a 27) (a 11) 0 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [8] := remove (a 27) 0 [0,8] d27 b3
  have b4 : a 13 ≠ 0 := exclude [2] (fun u v => edge r40 v u) (a 13) (a 12) 0 d12 c40 (by decide +kernel)
  have t4 : a 13 ∈ [4] := remove (a 13) 0 [0,4] d13 b4
  have b5 : a 28 ≠ 0 := exclude [2] (fun u v => edge r42 v u) (a 28) (a 12) 0 d12 c42 (by decide +kernel)
  have t5 : a 28 ∈ [4] := remove (a 28) 0 [0,4] d28 b5
  have b6 : a 30 ≠ 0 := exclude [2] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t6 : a 30 ∈ [2] := remove (a 30) 0 [0,2] d30 b6
  have b7 : a 31 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 31) (a 15) 0 t2 c47 (by decide +kernel)
  have t7 : a 31 ∈ [5] := remove (a 31) 0 [0,5] d31 b7
  have b8 : a 16 ≠ 0 := exclude [3] (edge r48) (a 16) (a 17) 0 d17 c48 (by decide +kernel)
  have t8 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b8
  have b9 : a 18 ≠ 0 := exclude [6] (edge r55) (a 18) (a 19) 0 d19 c55 (by decide +kernel)
  have t9 : a 18 ∈ [12] := remove (a 18) 0 [0,12] d18 b9
  have b10 : a 23 ≠ 0 := exclude [6] (fun u v => edge r58 v u) (a 23) (a 19) 0 d19 c58 (by decide +kernel)
  have t10 : a 23 ∈ [9] := remove (a 23) 0 [0,9] d23 b10
  have b11 : a 21 ≠ 0 := exclude [9] (fun u v => edge r60 v u) (a 21) (a 20) 0 d20 c60 (by decide +kernel)
  have t11 : a 21 ∈ [18] := remove (a 21) 0 [0,18] d21 b11
  have b12 : a 29 ≠ 0 := exclude [10] (fun u v => edge r72 v u) (a 29) (a 25) 0 t0 c72 (by decide +kernel)
  have t12 : a 29 ∈ [10] := remove (a 29) 0 [0,10] d29 b12
  have b13 : a 2 ≠ 0 := exclude [8] (edge r10) (a 2) (a 6) 0 d6 c10 (by decide +kernel)
  have t13 : a 2 ∈ [8] := remove (a 2) 0 [0,8] d2 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
#print axioms chunk24
end PartitionCover205_187
