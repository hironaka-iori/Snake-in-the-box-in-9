import PartitionData205_229
namespace PartitionCover205_229
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,1,2,3])
    (d2 : a 2 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d3 : a 3 ∈ [0,1])
    (d34 : a 34 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d23 : a 23 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d38 : a 38 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2,3])
    (c13 : edge r13 (a 2) (a 10)=true)
    (c17 : edge r17 (a 3) (a 17)=true)
    (c29 : edge r29 (a 6) (a 34)=true)
    (c38 : edge r38 (a 9) (a 23)=true)
    (c41 : edge r41 (a 10) (a 24)=true)
    (c42 : edge r42 (a 10) (a 38)=true)
    (c63 : edge r63 (a 17) (a 21)=true)
    (c64 : edge r64 (a 17) (a 25)=true)
    (c70 : edge r70 (a 19) (a 21)=true)
    (c75 : edge r75 (a 21) (a 28)=true)
    (c77 : edge r77 (a 22) (a 23)=true)
    : a 10 ∈ [0,2] ∧ a 17 ∈ [0] ∧ a 34 ∈ [0,2] ∧ a 23 ∈ [0,2] ∧ a 24 ∈ [0] ∧ a 38 ∈ [0,2] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0,2] ∧ a 19 ∈ [0] ∧ a 28 ∈ [0] ∧ a 22 ∈ [0,2,3] := by
  have b0 : a 10 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 1 d2 c13 (by decide +kernel)
  have t0 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b0
  have b1 : a 10 ≠ 3 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 3 d2 c13 (by decide +kernel)
  have t1 : a 10 ∈ [0,2] := remove (a 10) 3 [0,2,3] t0 b1
  have b2 : a 17 ≠ 1 := exclude [0,1] (fun u v => edge r17 v u) (a 17) (a 3) 1 d3 c17 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b2
  have b3 : a 34 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 34) (a 6) 1 d6 c29 (by decide +kernel)
  have t3 : a 34 ∈ [0,2,3] := remove (a 34) 1 [0,1,2,3] d34 b3
  have b4 : a 34 ≠ 3 := exclude [0] (fun u v => edge r29 v u) (a 34) (a 6) 3 d6 c29 (by decide +kernel)
  have t4 : a 34 ∈ [0,2] := remove (a 34) 3 [0,2,3] t3 b4
  have b5 : a 23 ≠ 1 := exclude [0,1] (fun u v => edge r38 v u) (a 23) (a 9) 1 d9 c38 (by decide +kernel)
  have t5 : a 23 ∈ [0,2,3] := remove (a 23) 1 [0,1,2,3] d23 b5
  have b6 : a 23 ≠ 3 := exclude [0,1] (fun u v => edge r38 v u) (a 23) (a 9) 3 d9 c38 (by decide +kernel)
  have t6 : a 23 ∈ [0,2] := remove (a 23) 3 [0,2,3] t5 b6
  have b7 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r41 v u) (a 24) (a 10) 1 t1 c41 (by decide +kernel)
  have t7 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b7
  have b8 : a 38 ≠ 1 := exclude [0,2] (fun u v => edge r42 v u) (a 38) (a 10) 1 t1 c42 (by decide +kernel)
  have t8 : a 38 ∈ [0,2,3] := remove (a 38) 1 [0,1,2,3] d38 b8
  have b9 : a 38 ≠ 3 := exclude [0,2] (fun u v => edge r42 v u) (a 38) (a 10) 3 t1 c42 (by decide +kernel)
  have t9 : a 38 ∈ [0,2] := remove (a 38) 3 [0,2,3] t8 b9
  have b10 : a 21 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 21) (a 17) 1 t2 c63 (by decide +kernel)
  have t10 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b10
  have b11 : a 25 ≠ 1 := exclude [0] (fun u v => edge r64 v u) (a 25) (a 17) 1 t2 c64 (by decide +kernel)
  have t11 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b11
  have b12 : a 25 ≠ 3 := exclude [0] (fun u v => edge r64 v u) (a 25) (a 17) 3 t2 c64 (by decide +kernel)
  have t12 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t11 b12
  have b13 : a 19 ≠ 1 := exclude [0] (edge r70) (a 19) (a 21) 1 t10 c70 (by decide +kernel)
  have t13 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b13
  have b14 : a 28 ≠ 1 := exclude [0] (fun u v => edge r75 v u) (a 28) (a 21) 1 t10 c75 (by decide +kernel)
  have t14 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b14
  have b15 : a 22 ≠ 1 := exclude [0,2] (edge r77) (a 22) (a 23) 1 t6 c77 (by decide +kernel)
  have t15 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b15
  exact And.intro t1 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t13 (And.intro t14 (t15))))))))))

theorem chunk1 (a : Nat → Nat)
    (d22 : a 22 ∈ [0,2,3])
    (d23 : a 23 ∈ [0,2])
    (d26 : a 26 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d54 : a 54 ∈ [0,1,2,3])
    (d57 : a 57 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d32 : a 32 ∈ [0,1])
    (d34 : a 34 ∈ [0,2])
    (d40 : a 40 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d36 : a 36 ∈ [0,1])
    (d38 : a 38 ∈ [0,2])
    (d41 : a 41 ∈ [0,1])
    (d55 : a 55 ∈ [0,1,2,3])
    (c77 : edge r77 (a 22) (a 23)=true)
    (c79 : edge r79 (a 22) (a 26)=true)
    (c81 : edge r81 (a 23) (a 51)=true)
    (c84 : edge r84 (a 24) (a 52)=true)
    (c88 : edge r88 (a 26) (a 54)=true)
    (c91 : edge r91 (a 28) (a 57)=true)
    (c104 : edge r104 (a 32) (a 34)=true)
    (c105 : edge r105 (a 32) (a 40)=true)
    (c110 : edge r110 (a 34) (a 35)=true)
    (c111 : edge r111 (a 34) (a 49)=true)
    (c112 : edge r112 (a 35) (a 42)=true)
    (c115 : edge r115 (a 36) (a 38)=true)
    (c124 : edge r124 (a 40) (a 41)=true)
    (c127 : edge r127 (a 41) (a 55)=true)
    : a 22 ∈ [0,2] ∧ a 26 ∈ [0] ∧ a 51 ∈ [0] ∧ a 52 ∈ [0] ∧ a 54 ∈ [0,2] ∧ a 57 ∈ [0] ∧ a 32 ∈ [0] ∧ a 40 ∈ [0] ∧ a 35 ∈ [0] ∧ a 49 ∈ [0] ∧ a 42 ∈ [0] ∧ a 36 ∈ [0] ∧ a 41 ∈ [0] ∧ a 55 ∈ [0,2] := by
  have b0 : a 22 ≠ 3 := exclude [0,2] (edge r77) (a 22) (a 23) 3 d23 c77 (by decide +kernel)
  have t0 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] d22 b0
  have b1 : a 26 ≠ 1 := exclude [0,2] (fun u v => edge r79 v u) (a 26) (a 22) 1 t0 c79 (by decide +kernel)
  have t1 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b1
  have b2 : a 51 ≠ 1 := exclude [0,2] (fun u v => edge r81 v u) (a 51) (a 23) 1 d23 c81 (by decide +kernel)
  have t2 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b2
  have b3 : a 52 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 52) (a 24) 1 d24 c84 (by decide +kernel)
  have t3 : a 52 ∈ [0] := remove (a 52) 1 [0,1] d52 b3
  have b4 : a 54 ≠ 1 := exclude [0] (fun u v => edge r88 v u) (a 54) (a 26) 1 t1 c88 (by decide +kernel)
  have t4 : a 54 ∈ [0,2,3] := remove (a 54) 1 [0,1,2,3] d54 b4
  have b5 : a 54 ≠ 3 := exclude [0] (fun u v => edge r88 v u) (a 54) (a 26) 3 t1 c88 (by decide +kernel)
  have t5 : a 54 ∈ [0,2] := remove (a 54) 3 [0,2,3] t4 b5
  have b6 : a 57 ≠ 1 := exclude [0] (fun u v => edge r91 v u) (a 57) (a 28) 1 d28 c91 (by decide +kernel)
  have t6 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b6
  have b7 : a 32 ≠ 1 := exclude [0,2] (edge r104) (a 32) (a 34) 1 d34 c104 (by decide +kernel)
  have t7 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b7
  have b8 : a 40 ≠ 1 := exclude [0] (fun u v => edge r105 v u) (a 40) (a 32) 1 t7 c105 (by decide +kernel)
  have t8 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b8
  have b9 : a 35 ≠ 1 := exclude [0,2] (fun u v => edge r110 v u) (a 35) (a 34) 1 d34 c110 (by decide +kernel)
  have t9 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b9
  have b10 : a 49 ≠ 1 := exclude [0,2] (fun u v => edge r111 v u) (a 49) (a 34) 1 d34 c111 (by decide +kernel)
  have t10 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b10
  have b11 : a 42 ≠ 1 := exclude [0] (fun u v => edge r112 v u) (a 42) (a 35) 1 t9 c112 (by decide +kernel)
  have t11 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b11
  have b12 : a 36 ≠ 1 := exclude [0,2] (edge r115) (a 36) (a 38) 1 d38 c115 (by decide +kernel)
  have t12 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b12
  have b13 : a 41 ≠ 1 := exclude [0] (fun u v => edge r124 v u) (a 41) (a 40) 1 t8 c124 (by decide +kernel)
  have t13 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b13
  have b14 : a 55 ≠ 1 := exclude [0] (fun u v => edge r127 v u) (a 55) (a 41) 1 t13 c127 (by decide +kernel)
  have t14 : a 55 ∈ [0,2,3] := remove (a 55) 1 [0,1,2,3] d55 b14
  have b15 : a 55 ≠ 3 := exclude [0] (fun u v => edge r127 v u) (a 55) (a 41) 3 t13 c127 (by decide +kernel)
  have t15 : a 55 ∈ [0,2] := remove (a 55) 3 [0,2,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (t15)))))))))))))

theorem chunk2 (a : Nat → Nat)
    (d44 : a 44 ∈ [0,1])
    (d51 : a 51 ∈ [0])
    (d45 : a 45 ∈ [0,1])
    (d49 : a 49 ∈ [0])
    (d56 : a 56 ∈ [0,1,2,3])
    (d13 : a 13 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0])
    (d18 : a 18 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d33 : a 33 ∈ [0,1])
    (d32 : a 32 ∈ [0])
    (d43 : a 43 ∈ [0,1])
    (c48 : edge r48 (a 13) (a 28)=true)
    (c66 : edge r66 (a 18) (a 19)=true)
    (c103 : edge r103 (a 32) (a 33)=true)
    (c129 : edge r129 (a 43) (a 44)=true)
    (c134 : edge r134 (a 44) (a 51)=true)
    (c136 : edge r136 (a 45) (a 49)=true)
    (c146 : edge r146 (a 49) (a 56)=true)
    : a 44 ∈ [0] ∧ a 45 ∈ [0] ∧ a 56 ∈ [0,2] ∧ a 13 ∈ [0,2] ∧ a 18 ∈ [0] ∧ a 33 ∈ [0] ∧ a 43 ∈ [0] := by
  have b0 : a 44 ≠ 1 := exclude [0] (edge r134) (a 44) (a 51) 1 d51 c134 (by decide +kernel)
  have t0 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b0
  have b1 : a 45 ≠ 1 := exclude [0] (edge r136) (a 45) (a 49) 1 d49 c136 (by decide +kernel)
  have t1 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b1
  have b2 : a 56 ≠ 1 := exclude [0] (fun u v => edge r146 v u) (a 56) (a 49) 1 d49 c146 (by decide +kernel)
  have t2 : a 56 ∈ [0,2,3] := remove (a 56) 1 [0,1,2,3] d56 b2
  have b3 : a 56 ≠ 3 := exclude [0] (fun u v => edge r146 v u) (a 56) (a 49) 3 d49 c146 (by decide +kernel)
  have t3 : a 56 ∈ [0,2] := remove (a 56) 3 [0,2,3] t2 b3
  have b4 : a 13 ≠ 1 := exclude [0] (edge r48) (a 13) (a 28) 1 d28 c48 (by decide +kernel)
  have t4 : a 13 ∈ [0,2,3] := remove (a 13) 1 [0,1,2,3] d13 b4
  have b5 : a 13 ≠ 3 := exclude [0] (edge r48) (a 13) (a 28) 3 d28 c48 (by decide +kernel)
  have t5 : a 13 ∈ [0,2] := remove (a 13) 3 [0,2,3] t4 b5
  have b6 : a 18 ≠ 1 := exclude [0] (edge r66) (a 18) (a 19) 1 d19 c66 (by decide +kernel)
  have t6 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b6
  have b7 : a 33 ≠ 1 := exclude [0] (fun u v => edge r103 v u) (a 33) (a 32) 1 d32 c103 (by decide +kernel)
  have t7 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b7
  have b8 : a 43 ≠ 1 := exclude [0] (edge r129) (a 43) (a 44) 1 t0 c129 (by decide +kernel)
  have t8 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b8
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))

theorem chunk3 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d27 : a 27 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d56 : a 56 ∈ [0,2])
    (d54 : a 54 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d38 : a 38 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (c16 : edge r16 (a 3) (a 7)=true)
    (c18 : edge r18 (a 4) (a 5)=true)
    (c20 : edge r20 (a 4) (a 11)=true)
    (c23 : edge r23 (a 5) (a 7)=true)
    (c30 : edge r30 (a 7) (a 13)=true)
    (c35 : edge r35 (a 8) (a 11)=true)
    (c36 : edge r36 (a 8) (a 22)=true)
    (c40 : edge r40 (a 10) (a 12)=true)
    (c42 : edge r42 (a 10) (a 38)=true)
    (c46 : edge r46 (a 12) (a 13)=true)
    (c47 : edge r47 (a 12) (a 27)=true)
    (c53 : edge r53 (a 14) (a 22)=true)
    (c60 : edge r60 (a 16) (a 20)=true)
    (c73 : edge r73 (a 20) (a 27)=true)
    (c90 : edge r90 (a 27) (a 56)=true)
    (c154 : edge r154 (a 54) (a 56)=true)
    : a 7 ∈ [0] ∧ a 5 ∈ [0] ∧ a 13 ∈ [0] ∧ a 12 ∈ [0] ∧ a 27 ∈ [0] ∧ a 20 ∈ [0] ∧ a 56 ∈ [0] ∧ a 54 ∈ [0] ∧ a 4 ∈ [0] ∧ a 11 ∈ [0] ∧ a 8 ∈ [0] ∧ a 22 ∈ [0] ∧ a 10 ∈ [0] ∧ a 38 ∈ [0] ∧ a 14 ∈ [0] ∧ a 16 ∈ [0] := by
  have b0 : a 7 ≠ 1 := exclude [0] (fun u v => edge r16 v u) (a 7) (a 3) 1 d3 c16 (by decide +kernel)
  have t0 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b0
  have b1 : a 5 ≠ 1 := exclude [0] (edge r23) (a 5) (a 7) 1 t0 c23 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 13 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 13) (a 7) 2 t0 c30 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b2
  have b3 : a 12 ≠ 1 := exclude [0] (edge r46) (a 12) (a 13) 1 t2 c46 (by decide +kernel)
  have t3 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b3
  have b4 : a 27 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 27) (a 12) 1 t3 c47 (by decide +kernel)
  have t4 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b4
  have b5 : a 20 ≠ 1 := exclude [0] (edge r73) (a 20) (a 27) 1 t4 c73 (by decide +kernel)
  have t5 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b5
  have b6 : a 56 ≠ 2 := exclude [0] (fun u v => edge r90 v u) (a 56) (a 27) 2 t4 c90 (by decide +kernel)
  have t6 : a 56 ∈ [0] := remove (a 56) 2 [0,2] d56 b6
  have b7 : a 54 ≠ 2 := exclude [0] (edge r154) (a 54) (a 56) 2 t6 c154 (by decide +kernel)
  have t7 : a 54 ∈ [0] := remove (a 54) 2 [0,2] d54 b7
  have b8 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 5) 1 t1 c18 (by decide +kernel)
  have t8 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b8
  have b9 : a 11 ≠ 1 := exclude [0] (fun u v => edge r20 v u) (a 11) (a 4) 1 t8 c20 (by decide +kernel)
  have t9 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b9
  have b10 : a 8 ≠ 1 := exclude [0] (edge r35) (a 8) (a 11) 1 t9 c35 (by decide +kernel)
  have t10 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b10
  have b11 : a 22 ≠ 2 := exclude [0] (fun u v => edge r36 v u) (a 22) (a 8) 2 t10 c36 (by decide +kernel)
  have t11 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b11
  have b12 : a 10 ≠ 2 := exclude [0] (edge r40) (a 10) (a 12) 2 t3 c40 (by decide +kernel)
  have t12 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b12
  have b13 : a 38 ≠ 2 := exclude [0] (fun u v => edge r42 v u) (a 38) (a 10) 2 t12 c42 (by decide +kernel)
  have t13 : a 38 ∈ [0] := remove (a 38) 2 [0,2] d38 b13
  have b14 : a 14 ≠ 1 := exclude [0] (edge r53) (a 14) (a 22) 1 t11 c53 (by decide +kernel)
  have t14 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b14
  have b15 : a 16 ≠ 1 := exclude [0] (edge r60) (a 16) (a 20) 1 t5 c60 (by decide +kernel)
  have t15 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_229
