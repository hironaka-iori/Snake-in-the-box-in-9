import PartitionData205_235
namespace PartitionCover205_235
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [1])
    (d23 : a 23 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d10 : a 10 ∈ [1])
    (d25 : a 25 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d12 : a 12 ∈ [1])
    (d29 : a 29 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d16 : a 16 ∈ [1])
    (d46 : a 46 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d17 : a 17 ∈ [2])
    (d48 : a 48 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d20 : a 20 ∈ [2])
    (d51 : a 51 ∈ [0,1])
    (c35 : edge r35 (a 8) (a 9)=true)
    (c38 : edge r38 (a 8) (a 23)=true)
    (c42 : edge r42 (a 9) (a 24)=true)
    (c43 : edge r43 (a 9) (a 40)=true)
    (c45 : edge r45 (a 10) (a 14)=true)
    (c46 : edge r46 (a 10) (a 25)=true)
    (c47 : edge r47 (a 10) (a 41)=true)
    (c53 : edge r53 (a 12) (a 43)=true)
    (c56 : edge r56 (a 14) (a 29)=true)
    (c57 : edge r57 (a 14) (a 45)=true)
    (c58 : edge r58 (a 15) (a 16)=true)
    (c62 : edge r62 (a 15) (a 46)=true)
    (c68 : edge r68 (a 17) (a 21)=true)
    (c70 : edge r70 (a 17) (a 48)=true)
    (c79 : edge r79 (a 20) (a 28)=true)
    (c80 : edge r80 (a 20) (a 51)=true)
    : a 8 ∈ [1] ∧ a 23 ∈ [1] ∧ a 24 ∈ [1] ∧ a 40 ∈ [1] ∧ a 14 ∈ [1] ∧ a 25 ∈ [1] ∧ a 41 ∈ [1] ∧ a 43 ∈ [1] ∧ a 29 ∈ [1] ∧ a 45 ∈ [1] ∧ a 15 ∈ [1] ∧ a 46 ∈ [2] ∧ a 21 ∈ [1] ∧ a 48 ∈ [2] ∧ a 28 ∈ [1] ∧ a 51 ∈ [1] := by
  have b0 : a 8 ≠ 0 := exclude [1] (edge r35) (a 8) (a 9) 0 d9 c35 (by decide +kernel)
  have t0 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b0
  have b1 : a 23 ≠ 0 := exclude [1] (fun u v => edge r38 v u) (a 23) (a 8) 0 t0 c38 (by decide +kernel)
  have t1 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b1
  have b2 : a 24 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 24) (a 9) 0 d9 c42 (by decide +kernel)
  have t2 : a 24 ∈ [1] := remove (a 24) 0 [0,1] d24 b2
  have b3 : a 40 ≠ 0 := exclude [1] (fun u v => edge r43 v u) (a 40) (a 9) 0 d9 c43 (by decide +kernel)
  have t3 : a 40 ∈ [1] := remove (a 40) 0 [0,1] d40 b3
  have b4 : a 14 ≠ 0 := exclude [1] (fun u v => edge r45 v u) (a 14) (a 10) 0 d10 c45 (by decide +kernel)
  have t4 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b4
  have b5 : a 25 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 25) (a 10) 0 d10 c46 (by decide +kernel)
  have t5 : a 25 ∈ [1] := remove (a 25) 0 [0,1] d25 b5
  have b6 : a 41 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 41) (a 10) 0 d10 c47 (by decide +kernel)
  have t6 : a 41 ∈ [1] := remove (a 41) 0 [0,1] d41 b6
  have b7 : a 43 ≠ 0 := exclude [1] (fun u v => edge r53 v u) (a 43) (a 12) 0 d12 c53 (by decide +kernel)
  have t7 : a 43 ∈ [1] := remove (a 43) 0 [0,1] d43 b7
  have b8 : a 29 ≠ 0 := exclude [1] (fun u v => edge r56 v u) (a 29) (a 14) 0 t4 c56 (by decide +kernel)
  have t8 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b8
  have b9 : a 45 ≠ 0 := exclude [1] (fun u v => edge r57 v u) (a 45) (a 14) 0 t4 c57 (by decide +kernel)
  have t9 : a 45 ∈ [1] := remove (a 45) 0 [0,1] d45 b9
  have b10 : a 15 ≠ 0 := exclude [1] (edge r58) (a 15) (a 16) 0 d16 c58 (by decide +kernel)
  have t10 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b10
  have b11 : a 46 ≠ 0 := exclude [1] (fun u v => edge r62 v u) (a 46) (a 15) 0 t10 c62 (by decide +kernel)
  have t11 : a 46 ∈ [2] := remove (a 46) 0 [0,2] d46 b11
  have b12 : a 21 ≠ 0 := exclude [2] (fun u v => edge r68 v u) (a 21) (a 17) 0 d17 c68 (by decide +kernel)
  have t12 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b12
  have b13 : a 48 ≠ 0 := exclude [2] (fun u v => edge r70 v u) (a 48) (a 17) 0 d17 c70 (by decide +kernel)
  have t13 : a 48 ∈ [2] := remove (a 48) 0 [0,2] d48 b13
  have b14 : a 28 ≠ 0 := exclude [2] (fun u v => edge r79 v u) (a 28) (a 20) 0 d20 c79 (by decide +kernel)
  have t14 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b14
  have b15 : a 51 ≠ 0 := exclude [2] (fun u v => edge r80 v u) (a 51) (a 20) 0 d20 c80 (by decide +kernel)
  have t15 : a 51 ∈ [1] := remove (a 51) 0 [0,1] d51 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1])
    (d22 : a 22 ∈ [2])
    (d53 : a 53 ∈ [0,2])
    (d54 : a 54 ∈ [0,1])
    (d24 : a 24 ∈ [1])
    (d55 : a 55 ∈ [0,2])
    (d25 : a 25 ∈ [1])
    (d58 : a 58 ∈ [0,1])
    (d28 : a 28 ∈ [1])
    (d60 : a 60 ∈ [0,1])
    (d31 : a 31 ∈ [0,2])
    (d32 : a 32 ∈ [1])
    (d37 : a 37 ∈ [0,1])
    (d33 : a 33 ∈ [1])
    (d50 : a 50 ∈ [0,1])
    (d35 : a 35 ∈ [1])
    (d44 : a 44 ∈ [0,1])
    (d40 : a 40 ∈ [1])
    (d49 : a 49 ∈ [0,1])
    (d48 : a 48 ∈ [2])
    (d56 : a 56 ∈ [0,1])
    (c84 : edge r84 (a 22) (a 30)=true)
    (c85 : edge r85 (a 22) (a 53)=true)
    (c91 : edge r91 (a 24) (a 54)=true)
    (c94 : edge r94 (a 25) (a 55)=true)
    (c101 : edge r101 (a 28) (a 58)=true)
    (c104 : edge r104 (a 30) (a 60)=true)
    (c105 : edge r105 (a 31) (a 32)=true)
    (c115 : edge r115 (a 33) (a 37)=true)
    (c124 : edge r124 (a 35) (a 50)=true)
    (c136 : edge r136 (a 40) (a 44)=true)
    (c153 : edge r153 (a 48) (a 49)=true)
    (c157 : edge r157 (a 49) (a 56)=true)
    : a 30 ∈ [1] ∧ a 53 ∈ [2] ∧ a 54 ∈ [1] ∧ a 55 ∈ [2] ∧ a 58 ∈ [1] ∧ a 60 ∈ [1] ∧ a 31 ∈ [2] ∧ a 37 ∈ [1] ∧ a 50 ∈ [1] ∧ a 44 ∈ [1] ∧ a 49 ∈ [1] ∧ a 56 ∈ [1] := by
  have b0 : a 30 ≠ 0 := exclude [2] (fun u v => edge r84 v u) (a 30) (a 22) 0 d22 c84 (by decide +kernel)
  have t0 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b0
  have b1 : a 53 ≠ 0 := exclude [2] (fun u v => edge r85 v u) (a 53) (a 22) 0 d22 c85 (by decide +kernel)
  have t1 : a 53 ∈ [2] := remove (a 53) 0 [0,2] d53 b1
  have b2 : a 54 ≠ 0 := exclude [1] (fun u v => edge r91 v u) (a 54) (a 24) 0 d24 c91 (by decide +kernel)
  have t2 : a 54 ∈ [1] := remove (a 54) 0 [0,1] d54 b2
  have b3 : a 55 ≠ 0 := exclude [1] (fun u v => edge r94 v u) (a 55) (a 25) 0 d25 c94 (by decide +kernel)
  have t3 : a 55 ∈ [2] := remove (a 55) 0 [0,2] d55 b3
  have b4 : a 58 ≠ 0 := exclude [1] (fun u v => edge r101 v u) (a 58) (a 28) 0 d28 c101 (by decide +kernel)
  have t4 : a 58 ∈ [1] := remove (a 58) 0 [0,1] d58 b4
  have b5 : a 60 ≠ 0 := exclude [1] (fun u v => edge r104 v u) (a 60) (a 30) 0 t0 c104 (by decide +kernel)
  have t5 : a 60 ∈ [1] := remove (a 60) 0 [0,1] d60 b5
  have b6 : a 31 ≠ 0 := exclude [1] (edge r105) (a 31) (a 32) 0 d32 c105 (by decide +kernel)
  have t6 : a 31 ∈ [2] := remove (a 31) 0 [0,2] d31 b6
  have b7 : a 37 ≠ 0 := exclude [1] (fun u v => edge r115 v u) (a 37) (a 33) 0 d33 c115 (by decide +kernel)
  have t7 : a 37 ∈ [1] := remove (a 37) 0 [0,1] d37 b7
  have b8 : a 50 ≠ 0 := exclude [1] (fun u v => edge r124 v u) (a 50) (a 35) 0 d35 c124 (by decide +kernel)
  have t8 : a 50 ∈ [1] := remove (a 50) 0 [0,1] d50 b8
  have b9 : a 44 ≠ 0 := exclude [1] (fun u v => edge r136 v u) (a 44) (a 40) 0 d40 c136 (by decide +kernel)
  have t9 : a 44 ∈ [1] := remove (a 44) 0 [0,1] d44 b9
  have b10 : a 49 ≠ 0 := exclude [2] (fun u v => edge r153 v u) (a 49) (a 48) 0 d48 c153 (by decide +kernel)
  have t10 : a 49 ∈ [1] := remove (a 49) 0 [0,1] d49 b10
  have b11 : a 56 ≠ 0 := exclude [1] (fun u v => edge r157 v u) (a 56) (a 49) 0 t10 c157 (by decide +kernel)
  have t11 : a 56 ∈ [1] := remove (a 56) 0 [0,1] d56 b11
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t11)))))))))))
#print axioms chunk8
#print axioms chunk9
end PartitionCover205_235
