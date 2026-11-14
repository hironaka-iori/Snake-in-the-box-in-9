import PartitionData205_185
namespace PartitionCover205_185
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk24 (a : Nat → Nat)
    (d15 : a 15 ∈ [0,2])
    (d11 : a 11 ∈ [18])
    (d27 : a 27 ∈ [0,9])
    (d28 : a 28 ∈ [0,14])
    (d12 : a 12 ∈ [9])
    (d30 : a 30 ∈ [0,4])
    (d14 : a 14 ∈ [4])
    (d31 : a 31 ∈ [0,6])
    (d16 : a 16 ∈ [0,1])
    (d18 : a 18 ∈ [3])
    (d20 : a 20 ∈ [0,2])
    (d24 : a 24 ∈ [0,4])
    (d17 : a 17 ∈ [0,2])
    (d25 : a 25 ∈ [2])
    (d21 : a 21 ∈ [0,4])
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [1])
    (d29 : a 29 ∈ [0,4])
    (d4 : a 4 ∈ [0,3])
    (d5 : a 5 ∈ [0,12])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c49 : edge r49 (a 16) (a 18)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    : a 15 ∈ [2] ∧ a 27 ∈ [9] ∧ a 28 ∈ [14] ∧ a 30 ∈ [4] ∧ a 31 ∈ [6] ∧ a 16 ∈ [1] ∧ a 20 ∈ [2] ∧ a 24 ∈ [4] ∧ a 17 ∈ [2] ∧ a 21 ∈ [4] ∧ a 23 ∈ [1] ∧ a 29 ∈ [4] ∧ a 4 ∈ [3] ∧ a 5 ∈ [12] := by
  have b0 : a 15 ≠ 0 := exclude [18] (fun u v => edge r38 v u) (a 15) (a 11) 0 d11 c38 (by decide +kernel)
  have t0 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b0
  have b1 : a 27 ≠ 0 := exclude [18] (fun u v => edge r39 v u) (a 27) (a 11) 0 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [9] := remove (a 27) 0 [0,9] d27 b1
  have b2 : a 28 ≠ 0 := exclude [9] (fun u v => edge r42 v u) (a 28) (a 12) 0 d12 c42 (by decide +kernel)
  have t2 : a 28 ∈ [14] := remove (a 28) 0 [0,14] d28 b2
  have b3 : a 30 ≠ 0 := exclude [4] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t3 : a 30 ∈ [4] := remove (a 30) 0 [0,4] d30 b3
  have b4 : a 31 ≠ 0 := exclude [2] (fun u v => edge r47 v u) (a 31) (a 15) 0 t0 c47 (by decide +kernel)
  have t4 : a 31 ∈ [6] := remove (a 31) 0 [0,6] d31 b4
  have b5 : a 16 ≠ 0 := exclude [3] (edge r49) (a 16) (a 18) 0 d18 c49 (by decide +kernel)
  have t5 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b5
  have b6 : a 20 ≠ 0 := exclude [1] (fun u v => edge r50 v u) (a 20) (a 16) 0 t5 c50 (by decide +kernel)
  have t6 : a 20 ∈ [2] := remove (a 20) 0 [0,2] d20 b6
  have b7 : a 24 ≠ 0 := exclude [1] (fun u v => edge r51 v u) (a 24) (a 16) 0 t5 c51 (by decide +kernel)
  have t7 : a 24 ∈ [4] := remove (a 24) 0 [0,4] d24 b7
  have b8 : a 17 ≠ 0 := exclude [2] (edge r54) (a 17) (a 25) 0 d25 c54 (by decide +kernel)
  have t8 : a 17 ∈ [2] := remove (a 17) 0 [0,2] d17 b8
  have b9 : a 21 ≠ 0 := exclude [2] (fun u v => edge r60 v u) (a 21) (a 20) 0 t6 c60 (by decide +kernel)
  have t9 : a 21 ∈ [4] := remove (a 21) 0 [0,4] d21 b9
  have b10 : a 23 ≠ 0 := exclude [1] (fun u v => edge r65 v u) (a 23) (a 22) 0 d22 c65 (by decide +kernel)
  have t10 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b10
  have b11 : a 29 ≠ 0 := exclude [2] (fun u v => edge r72 v u) (a 29) (a 25) 0 d25 c72 (by decide +kernel)
  have t11 : a 29 ∈ [4] := remove (a 29) 0 [0,4] d29 b11
  have b12 : a 4 ≠ 0 := exclude [9] (edge r18) (a 4) (a 12) 0 d12 c18 (by decide +kernel)
  have t12 : a 4 ∈ [3] := remove (a 4) 0 [0,3] d4 b12
  have b13 : a 5 ≠ 0 := exclude [3] (fun u v => edge r16 v u) (a 5) (a 4) 0 t12 c16 (by decide +kernel)
  have t13 : a 5 ∈ [12] := remove (a 5) 0 [0,12] d5 b13
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (t13)))))))))))))
#print axioms chunk24
end PartitionCover205_185
