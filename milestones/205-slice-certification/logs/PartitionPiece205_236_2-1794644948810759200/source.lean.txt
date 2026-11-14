import PartitionData205_236
namespace PartitionCover205_236
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2])
    (d11 : a 11 ∈ [2])
    (d35 : a 35 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d14 : a 14 ∈ [2])
    (d39 : a 39 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [1])
    (d40 : a 40 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d19 : a 19 ∈ [0,2])
    (d20 : a 20 ∈ [2])
    (d43 : a 43 ∈ [0,2])
    (d44 : a 44 ∈ [0,1])
    (d21 : a 21 ∈ [1])
    (d25 : a 25 ∈ [0,2])
    (d45 : a 45 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d27 : a 27 ∈ [1])
    (c32 : edge r32 (a 11) (a 24)=true)
    (c33 : edge r33 (a 11) (a 35)=true)
    (c38 : edge r38 (a 13) (a 14)=true)
    (c41 : edge r41 (a 13) (a 39)=true)
    (c43 : edge r43 (a 14) (a 22)=true)
    (c45 : edge r45 (a 15) (a 17)=true)
    (c47 : edge r47 (a 15) (a 40)=true)
    (c51 : edge r51 (a 17) (a 41)=true)
    (c54 : edge r54 (a 19) (a 20)=true)
    (c58 : edge r58 (a 20) (a 43)=true)
    (c61 : edge r61 (a 21) (a 44)=true)
    (c62 : edge r62 (a 22) (a 25)=true)
    (c63 : edge r63 (a 22) (a 45)=true)
    (c67 : edge r67 (a 24) (a 48)=true)
    (c68 : edge r68 (a 25) (a 49)=true)
    (c69 : edge r69 (a 26) (a 27)=true)
    : a 24 ∈ [2] ∧ a 35 ∈ [1] ∧ a 13 ∈ [2] ∧ a 39 ∈ [1] ∧ a 22 ∈ [2] ∧ a 15 ∈ [1] ∧ a 40 ∈ [1] ∧ a 41 ∈ [1] ∧ a 19 ∈ [2] ∧ a 43 ∈ [2] ∧ a 44 ∈ [1] ∧ a 25 ∈ [2] ∧ a 45 ∈ [1] ∧ a 48 ∈ [1] ∧ a 49 ∈ [1] ∧ a 26 ∈ [1] := by
  have b0 : a 24 ≠ 0 := exclude [2] (fun u v => edge r32 v u) (a 24) (a 11) 0 d11 c32 (by decide +kernel)
  have t0 : a 24 ∈ [2] := remove (a 24) 0 [0,2] d24 b0
  have b1 : a 35 ≠ 0 := exclude [2] (fun u v => edge r33 v u) (a 35) (a 11) 0 d11 c33 (by decide +kernel)
  have t1 : a 35 ∈ [1] := remove (a 35) 0 [0,1] d35 b1
  have b2 : a 13 ≠ 0 := exclude [2] (edge r38) (a 13) (a 14) 0 d14 c38 (by decide +kernel)
  have t2 : a 13 ∈ [2] := remove (a 13) 0 [0,2] d13 b2
  have b3 : a 39 ≠ 0 := exclude [2] (fun u v => edge r41 v u) (a 39) (a 13) 0 t2 c41 (by decide +kernel)
  have t3 : a 39 ∈ [1] := remove (a 39) 0 [0,1] d39 b3
  have b4 : a 22 ≠ 0 := exclude [2] (fun u v => edge r43 v u) (a 22) (a 14) 0 d14 c43 (by decide +kernel)
  have t4 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b4
  have b5 : a 15 ≠ 0 := exclude [1] (edge r45) (a 15) (a 17) 0 d17 c45 (by decide +kernel)
  have t5 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b5
  have b6 : a 40 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 40) (a 15) 0 t5 c47 (by decide +kernel)
  have t6 : a 40 ∈ [1] := remove (a 40) 0 [0,1] d40 b6
  have b7 : a 41 ≠ 0 := exclude [1] (fun u v => edge r51 v u) (a 41) (a 17) 0 d17 c51 (by decide +kernel)
  have t7 : a 41 ∈ [1] := remove (a 41) 0 [0,1] d41 b7
  have b8 : a 19 ≠ 0 := exclude [2] (edge r54) (a 19) (a 20) 0 d20 c54 (by decide +kernel)
  have t8 : a 19 ∈ [2] := remove (a 19) 0 [0,2] d19 b8
  have b9 : a 43 ≠ 0 := exclude [2] (fun u v => edge r58 v u) (a 43) (a 20) 0 d20 c58 (by decide +kernel)
  have t9 : a 43 ∈ [2] := remove (a 43) 0 [0,2] d43 b9
  have b10 : a 44 ≠ 0 := exclude [1] (fun u v => edge r61 v u) (a 44) (a 21) 0 d21 c61 (by decide +kernel)
  have t10 : a 44 ∈ [1] := remove (a 44) 0 [0,1] d44 b10
  have b11 : a 25 ≠ 0 := exclude [2] (fun u v => edge r62 v u) (a 25) (a 22) 0 t4 c62 (by decide +kernel)
  have t11 : a 25 ∈ [2] := remove (a 25) 0 [0,2] d25 b11
  have b12 : a 45 ≠ 0 := exclude [2] (fun u v => edge r63 v u) (a 45) (a 22) 0 t4 c63 (by decide +kernel)
  have t12 : a 45 ∈ [1] := remove (a 45) 0 [0,1] d45 b12
  have b13 : a 48 ≠ 0 := exclude [2] (fun u v => edge r67 v u) (a 48) (a 24) 0 t0 c67 (by decide +kernel)
  have t13 : a 48 ∈ [1] := remove (a 48) 0 [0,1] d48 b13
  have b14 : a 49 ≠ 0 := exclude [2] (fun u v => edge r68 v u) (a 49) (a 25) 0 t11 c68 (by decide +kernel)
  have t14 : a 49 ∈ [1] := remove (a 49) 0 [0,1] d49 b14
  have b15 : a 26 ≠ 0 := exclude [1] (edge r69) (a 26) (a 27) 0 d27 c69 (by decide +kernel)
  have t15 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d32 : a 32 ∈ [0,1])
    (d27 : a 27 ∈ [1])
    (d28 : a 28 ∈ [0,1])
    (d33 : a 33 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d31 : a 31 ∈ [1])
    (d36 : a 36 ∈ [0,1])
    (d37 : a 37 ∈ [0,2])
    (d39 : a 39 ∈ [1])
    (d38 : a 38 ∈ [0,2])
    (d43 : a 43 ∈ [2])
    (d42 : a 42 ∈ [0,1])
    (d41 : a 41 ∈ [1])
    (d47 : a 47 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d13 : a 13 ∈ [2])
    (d16 : a 16 ∈ [0,1])
    (d15 : a 15 ∈ [1])
    (d29 : a 29 ∈ [0,1])
    (c34 : edge r34 (a 12) (a 13)=true)
    (c44 : edge r44 (a 15) (a 16)=true)
    (c71 : edge r71 (a 27) (a 32)=true)
    (c72 : edge r72 (a 28) (a 29)=true)
    (c73 : edge r73 (a 28) (a 33)=true)
    (c76 : edge r76 (a 30) (a 31)=true)
    (c81 : edge r81 (a 32) (a 36)=true)
    (c92 : edge r92 (a 37) (a 39)=true)
    (c94 : edge r94 (a 38) (a 43)=true)
    (c99 : edge r99 (a 41) (a 42)=true)
    (c103 : edge r103 (a 43) (a 47)=true)
    : a 32 ∈ [1] ∧ a 28 ∈ [1] ∧ a 30 ∈ [1] ∧ a 36 ∈ [1] ∧ a 37 ∈ [2] ∧ a 38 ∈ [2] ∧ a 42 ∈ [1] ∧ a 47 ∈ [2] ∧ a 12 ∈ [1] ∧ a 16 ∈ [1] ∧ a 29 ∈ [1] := by
  have b0 : a 32 ≠ 0 := exclude [1] (fun u v => edge r71 v u) (a 32) (a 27) 0 d27 c71 (by decide +kernel)
  have t0 : a 32 ∈ [1] := remove (a 32) 0 [0,1] d32 b0
  have b1 : a 28 ≠ 0 := exclude [1] (edge r73) (a 28) (a 33) 0 d33 c73 (by decide +kernel)
  have t1 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b1
  have b2 : a 30 ≠ 0 := exclude [1] (edge r76) (a 30) (a 31) 0 d31 c76 (by decide +kernel)
  have t2 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b2
  have b3 : a 36 ≠ 0 := exclude [1] (fun u v => edge r81 v u) (a 36) (a 32) 0 t0 c81 (by decide +kernel)
  have t3 : a 36 ∈ [1] := remove (a 36) 0 [0,1] d36 b3
  have b4 : a 37 ≠ 0 := exclude [1] (edge r92) (a 37) (a 39) 0 d39 c92 (by decide +kernel)
  have t4 : a 37 ∈ [2] := remove (a 37) 0 [0,2] d37 b4
  have b5 : a 38 ≠ 0 := exclude [2] (edge r94) (a 38) (a 43) 0 d43 c94 (by decide +kernel)
  have t5 : a 38 ∈ [2] := remove (a 38) 0 [0,2] d38 b5
  have b6 : a 42 ≠ 0 := exclude [1] (fun u v => edge r99 v u) (a 42) (a 41) 0 d41 c99 (by decide +kernel)
  have t6 : a 42 ∈ [1] := remove (a 42) 0 [0,1] d42 b6
  have b7 : a 47 ≠ 0 := exclude [2] (fun u v => edge r103 v u) (a 47) (a 43) 0 d43 c103 (by decide +kernel)
  have t7 : a 47 ∈ [2] := remove (a 47) 0 [0,2] d47 b7
  have b8 : a 12 ≠ 0 := exclude [2] (edge r34) (a 12) (a 13) 0 d13 c34 (by decide +kernel)
  have t8 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b8
  have b9 : a 16 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 16) (a 15) 0 d15 c44 (by decide +kernel)
  have t9 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b9
  have b10 : a 29 ≠ 0 := exclude [1] (fun u v => edge r72 v u) (a 29) (a 28) 0 t1 c72 (by decide +kernel)
  have t10 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b10
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (t10))))))))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_236
