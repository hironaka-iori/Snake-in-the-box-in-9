import PartitionData205_224
namespace PartitionCover205_224
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,1])
    (d17 : a 17 ∈ [1])
    (d48 : a 48 ∈ [0,2])
    (d51 : a 51 ∈ [0,2])
    (d20 : a 20 ∈ [2])
    (d28 : a 28 ∈ [0,1])
    (d21 : a 21 ∈ [1])
    (d52 : a 52 ∈ [0,2])
    (d22 : a 22 ∈ [0,2])
    (d24 : a 24 ∈ [2])
    (d23 : a 23 ∈ [0,2])
    (d54 : a 54 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d35 : a 35 ∈ [1])
    (d32 : a 32 ∈ [0,1])
    (d37 : a 37 ∈ [0,2])
    (d41 : a 41 ∈ [2])
    (d40 : a 40 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d44 : a 44 ∈ [0,2])
    (d43 : a 43 ∈ [1])
    (d49 : a 49 ∈ [0,1])
    (c65 : edge r65 (a 17) (a 25)=true)
    (c66 : edge r66 (a 17) (a 48)=true)
    (c75 : edge r75 (a 20) (a 51)=true)
    (c76 : edge r76 (a 21) (a 28)=true)
    (c77 : edge r77 (a 21) (a 52)=true)
    (c79 : edge r79 (a 22) (a 24)=true)
    (c81 : edge r81 (a 23) (a 25)=true)
    (c85 : edge r85 (a 24) (a 54)=true)
    (c87 : edge r87 (a 25) (a 55)=true)
    (c103 : edge r103 (a 31) (a 35)=true)
    (c108 : edge r108 (a 32) (a 48)=true)
    (c123 : edge r123 (a 37) (a 41)=true)
    (c131 : edge r131 (a 40) (a 55)=true)
    (c134 : edge r134 (a 41) (a 56)=true)
    (c137 : edge r137 (a 43) (a 44)=true)
    (c152 : edge r152 (a 49) (a 51)=true)
    : a 25 ∈ [1] ∧ a 48 ∈ [2] ∧ a 51 ∈ [2] ∧ a 28 ∈ [1] ∧ a 52 ∈ [2] ∧ a 22 ∈ [2] ∧ a 23 ∈ [2] ∧ a 54 ∈ [1] ∧ a 55 ∈ [1] ∧ a 31 ∈ [1] ∧ a 32 ∈ [1] ∧ a 37 ∈ [2] ∧ a 40 ∈ [1] ∧ a 56 ∈ [1] ∧ a 44 ∈ [2] ∧ a 49 ∈ [1] := by
  have b0 : a 25 ≠ 0 := exclude [1] (fun u v => edge r65 v u) (a 25) (a 17) 0 d17 c65 (by decide +kernel)
  have t0 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b0
  have b1 : a 48 ≠ 0 := exclude [1] (fun u v => edge r66 v u) (a 48) (a 17) 0 d17 c66 (by decide +kernel)
  have t1 : a 48 ∈ [2] := remove (a 48) 0 [0,2] d48 b1
  have b2 : a 51 ≠ 0 := exclude [2] (fun u v => edge r75 v u) (a 51) (a 20) 0 d20 c75 (by decide +kernel)
  have t2 : a 51 ∈ [2] := remove (a 51) 0 [0,2] d51 b2
  have b3 : a 28 ≠ 0 := exclude [1] (fun u v => edge r76 v u) (a 28) (a 21) 0 d21 c76 (by decide +kernel)
  have t3 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b3
  have b4 : a 52 ≠ 0 := exclude [1] (fun u v => edge r77 v u) (a 52) (a 21) 0 d21 c77 (by decide +kernel)
  have t4 : a 52 ∈ [2] := remove (a 52) 0 [0,2] d52 b4
  have b5 : a 22 ≠ 0 := exclude [2] (edge r79) (a 22) (a 24) 0 d24 c79 (by decide +kernel)
  have t5 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b5
  have b6 : a 23 ≠ 0 := exclude [1] (edge r81) (a 23) (a 25) 0 t0 c81 (by decide +kernel)
  have t6 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b6
  have b7 : a 54 ≠ 0 := exclude [2] (fun u v => edge r85 v u) (a 54) (a 24) 0 d24 c85 (by decide +kernel)
  have t7 : a 54 ∈ [1] := remove (a 54) 0 [0,1] d54 b7
  have b8 : a 55 ≠ 0 := exclude [1] (fun u v => edge r87 v u) (a 55) (a 25) 0 t0 c87 (by decide +kernel)
  have t8 : a 55 ∈ [1] := remove (a 55) 0 [0,1] d55 b8
  have b9 : a 31 ≠ 0 := exclude [1] (edge r103) (a 31) (a 35) 0 d35 c103 (by decide +kernel)
  have t9 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b9
  have b10 : a 32 ≠ 0 := exclude [2] (edge r108) (a 32) (a 48) 0 t1 c108 (by decide +kernel)
  have t10 : a 32 ∈ [1] := remove (a 32) 0 [0,1] d32 b10
  have b11 : a 37 ≠ 0 := exclude [2] (edge r123) (a 37) (a 41) 0 d41 c123 (by decide +kernel)
  have t11 : a 37 ∈ [2] := remove (a 37) 0 [0,2] d37 b11
  have b12 : a 40 ≠ 0 := exclude [1] (edge r131) (a 40) (a 55) 0 t8 c131 (by decide +kernel)
  have t12 : a 40 ∈ [1] := remove (a 40) 0 [0,1] d40 b12
  have b13 : a 56 ≠ 0 := exclude [2] (fun u v => edge r134 v u) (a 56) (a 41) 0 d41 c134 (by decide +kernel)
  have t13 : a 56 ∈ [1] := remove (a 56) 0 [0,1] d56 b13
  have b14 : a 44 ≠ 0 := exclude [1] (fun u v => edge r137 v u) (a 44) (a 43) 0 d43 c137 (by decide +kernel)
  have t14 : a 44 ∈ [2] := remove (a 44) 0 [0,2] d44 b14
  have b15 : a 49 ≠ 0 := exclude [2] (edge r152) (a 49) (a 51) 0 t2 c152 (by decide +kernel)
  have t15 : a 49 ∈ [1] := remove (a 49) 0 [0,1] d49 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d50 : a 50 ∈ [0,1])
    (d52 : a 52 ∈ [2])
    (d57 : a 57 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d16 : a 16 ∈ [1])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [1])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d32 : a 32 ∈ [1])
    (d38 : a 38 ∈ [0,1])
    (c52 : edge r52 (a 14) (a 16)=true)
    (c56 : edge r56 (a 15) (a 17)=true)
    (c94 : edge r94 (a 29) (a 31)=true)
    (c98 : edge r98 (a 30) (a 32)=true)
    (c100 : edge r100 (a 30) (a 38)=true)
    (c154 : edge r154 (a 50) (a 52)=true)
    (c155 : edge r155 (a 50) (a 57)=true)
    : a 50 ∈ [1] ∧ a 57 ∈ [1] ∧ a 14 ∈ [1] ∧ a 15 ∈ [1] ∧ a 29 ∈ [1] ∧ a 30 ∈ [1] ∧ a 38 ∈ [1] := by
  have b0 : a 50 ≠ 0 := exclude [2] (edge r154) (a 50) (a 52) 0 d52 c154 (by decide +kernel)
  have t0 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b0
  have b1 : a 57 ≠ 0 := exclude [1] (fun u v => edge r155 v u) (a 57) (a 50) 0 t0 c155 (by decide +kernel)
  have t1 : a 57 ∈ [1] := remove (a 57) 0 [0,1] d57 b1
  have b2 : a 14 ≠ 0 := exclude [1] (edge r52) (a 14) (a 16) 0 d16 c52 (by decide +kernel)
  have t2 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b2
  have b3 : a 15 ≠ 0 := exclude [1] (edge r56) (a 15) (a 17) 0 d17 c56 (by decide +kernel)
  have t3 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b3
  have b4 : a 29 ≠ 0 := exclude [1] (edge r94) (a 29) (a 31) 0 d31 c94 (by decide +kernel)
  have t4 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b4
  have b5 : a 30 ≠ 0 := exclude [1] (edge r98) (a 30) (a 32) 0 d32 c98 (by decide +kernel)
  have t5 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b5
  have b6 : a 38 ≠ 0 := exclude [1] (fun u v => edge r100 v u) (a 38) (a 30) 0 t5 c100 (by decide +kernel)
  have t6 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b6
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (t6))))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_224
