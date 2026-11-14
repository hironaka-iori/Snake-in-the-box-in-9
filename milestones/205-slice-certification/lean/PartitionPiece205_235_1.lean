import PartitionData205_235
namespace PartitionCover205_235
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d32 : a 32 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (d33 : a 33 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d22 : a 22 ∈ [0,2])
    (d38 : a 38 ∈ [0,1])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 9)=true)
    (c9 : edge r9 (a 1) (a 16)=true)
    (c10 : edge r10 (a 1) (a 32)=true)
    (c11 : edge r11 (a 2) (a 3)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 17)=true)
    (c15 : edge r15 (a 2) (a 33)=true)
    (c16 : edge r16 (a 3) (a 7)=true)
    (c20 : edge r20 (a 4) (a 5)=true)
    (c22 : edge r22 (a 4) (a 12)=true)
    (c24 : edge r24 (a 4) (a 35)=true)
    (c27 : edge r27 (a 5) (a 20)=true)
    (c33 : edge r33 (a 7) (a 22)=true)
    (c34 : edge r34 (a 7) (a 38)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 16 ∈ [0] ∧ a 32 ∈ [0] ∧ a 2 ∈ [0] ∧ a 10 ∈ [0] ∧ a 17 ∈ [0] ∧ a 33 ∈ [0] ∧ a 7 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 35 ∈ [0] ∧ a 20 ∈ [0] ∧ a 22 ∈ [0] ∧ a 38 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 3) (a 1) 1 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 5) (a 1) 2 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 2 [0,2] d5 b1
  have b2 : a 9 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 9) (a 1) 1 d1 c8 (by decide +kernel)
  have t2 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b2
  have b3 : a 16 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 16) (a 1) 1 d1 c9 (by decide +kernel)
  have t3 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b3
  have b4 : a 32 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 32) (a 1) 1 d1 c10 (by decide +kernel)
  have t4 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b4
  have b5 : a 2 ≠ 1 := exclude [0] (edge r11) (a 2) (a 3) 1 t0 c11 (by decide +kernel)
  have t5 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b5
  have b6 : a 10 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 1 t5 c13 (by decide +kernel)
  have t6 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b6
  have b7 : a 17 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 17) (a 2) 2 t5 c14 (by decide +kernel)
  have t7 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b7
  have b8 : a 33 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 33) (a 2) 1 t5 c15 (by decide +kernel)
  have t8 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b8
  have b9 : a 7 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 7) (a 3) 2 t0 c16 (by decide +kernel)
  have t9 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b9
  have b10 : a 4 ≠ 1 := exclude [0] (edge r20) (a 4) (a 5) 1 t1 c20 (by decide +kernel)
  have t10 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b10
  have b11 : a 12 ≠ 1 := exclude [0] (fun u v => edge r22 v u) (a 12) (a 4) 1 t10 c22 (by decide +kernel)
  have t11 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b11
  have b12 : a 35 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 35) (a 4) 1 t10 c24 (by decide +kernel)
  have t12 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b12
  have b13 : a 20 ≠ 2 := exclude [0] (fun u v => edge r27 v u) (a 20) (a 5) 2 t1 c27 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b13
  have b14 : a 22 ≠ 2 := exclude [0] (fun u v => edge r33 v u) (a 22) (a 7) 2 t9 c33 (by decide +kernel)
  have t14 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b14
  have b15 : a 38 ≠ 1 := exclude [0] (fun u v => edge r34 v u) (a 38) (a 7) 1 t9 c34 (by decide +kernel)
  have t15 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d8 : a 8 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d23 : a 23 ∈ [0,1])
    (d24 : a 24 ∈ [0,1])
    (d40 : a 40 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d25 : a 25 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d43 : a 43 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (d46 : a 46 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d48 : a 48 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d20 : a 20 ∈ [0])
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
    : a 8 ∈ [0] ∧ a 23 ∈ [0] ∧ a 24 ∈ [0] ∧ a 40 ∈ [0] ∧ a 14 ∈ [0] ∧ a 25 ∈ [0] ∧ a 41 ∈ [0] ∧ a 43 ∈ [0] ∧ a 29 ∈ [0] ∧ a 45 ∈ [0] ∧ a 15 ∈ [0] ∧ a 46 ∈ [0] ∧ a 21 ∈ [0] ∧ a 48 ∈ [0] ∧ a 28 ∈ [0] ∧ a 51 ∈ [0] := by
  have b0 : a 8 ≠ 1 := exclude [0] (edge r35) (a 8) (a 9) 1 d9 c35 (by decide +kernel)
  have t0 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b0
  have b1 : a 23 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 23) (a 8) 1 t0 c38 (by decide +kernel)
  have t1 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b1
  have b2 : a 24 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 24) (a 9) 1 d9 c42 (by decide +kernel)
  have t2 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b2
  have b3 : a 40 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 40) (a 9) 1 d9 c43 (by decide +kernel)
  have t3 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b3
  have b4 : a 14 ≠ 1 := exclude [0] (fun u v => edge r45 v u) (a 14) (a 10) 1 d10 c45 (by decide +kernel)
  have t4 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b4
  have b5 : a 25 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 25) (a 10) 1 d10 c46 (by decide +kernel)
  have t5 : a 25 ∈ [0] := remove (a 25) 1 [0,1] d25 b5
  have b6 : a 41 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 41) (a 10) 1 d10 c47 (by decide +kernel)
  have t6 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b6
  have b7 : a 43 ≠ 1 := exclude [0] (fun u v => edge r53 v u) (a 43) (a 12) 1 d12 c53 (by decide +kernel)
  have t7 : a 43 ∈ [0] := remove (a 43) 1 [0,1] d43 b7
  have b8 : a 29 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 29) (a 14) 1 t4 c56 (by decide +kernel)
  have t8 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b8
  have b9 : a 45 ≠ 1 := exclude [0] (fun u v => edge r57 v u) (a 45) (a 14) 1 t4 c57 (by decide +kernel)
  have t9 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b9
  have b10 : a 15 ≠ 1 := exclude [0] (edge r58) (a 15) (a 16) 1 d16 c58 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b10
  have b11 : a 46 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 46) (a 15) 2 t10 c62 (by decide +kernel)
  have t11 : a 46 ∈ [0] := remove (a 46) 2 [0,2] d46 b11
  have b12 : a 21 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 21) (a 17) 1 d17 c68 (by decide +kernel)
  have t12 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b12
  have b13 : a 48 ≠ 2 := exclude [0] (fun u v => edge r70 v u) (a 48) (a 17) 2 d17 c70 (by decide +kernel)
  have t13 : a 48 ∈ [0] := remove (a 48) 2 [0,2] d48 b13
  have b14 : a 28 ≠ 1 := exclude [0] (fun u v => edge r79 v u) (a 28) (a 20) 1 d20 c79 (by decide +kernel)
  have t14 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b14
  have b15 : a 51 ≠ 1 := exclude [0] (fun u v => edge r80 v u) (a 51) (a 20) 1 d20 c80 (by decide +kernel)
  have t15 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1])
    (d22 : a 22 ∈ [0])
    (d53 : a 53 ∈ [0,2])
    (d54 : a 54 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d55 : a 55 ∈ [0,2])
    (d25 : a 25 ∈ [0])
    (d58 : a 58 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d60 : a 60 ∈ [0,1])
    (d31 : a 31 ∈ [0,2])
    (d32 : a 32 ∈ [0])
    (d37 : a 37 ∈ [0,1])
    (d33 : a 33 ∈ [0])
    (d50 : a 50 ∈ [0,1])
    (d35 : a 35 ∈ [0])
    (d44 : a 44 ∈ [0,1])
    (d40 : a 40 ∈ [0])
    (d49 : a 49 ∈ [0,1])
    (d48 : a 48 ∈ [0])
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
    : a 30 ∈ [0] ∧ a 53 ∈ [0] ∧ a 54 ∈ [0] ∧ a 55 ∈ [0] ∧ a 58 ∈ [0] ∧ a 60 ∈ [0] ∧ a 31 ∈ [0] ∧ a 37 ∈ [0] ∧ a 50 ∈ [0] ∧ a 44 ∈ [0] ∧ a 49 ∈ [0] ∧ a 56 ∈ [0] := by
  have b0 : a 30 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 30) (a 22) 1 d22 c84 (by decide +kernel)
  have t0 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b0
  have b1 : a 53 ≠ 2 := exclude [0] (fun u v => edge r85 v u) (a 53) (a 22) 2 d22 c85 (by decide +kernel)
  have t1 : a 53 ∈ [0] := remove (a 53) 2 [0,2] d53 b1
  have b2 : a 54 ≠ 1 := exclude [0] (fun u v => edge r91 v u) (a 54) (a 24) 1 d24 c91 (by decide +kernel)
  have t2 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b2
  have b3 : a 55 ≠ 2 := exclude [0] (fun u v => edge r94 v u) (a 55) (a 25) 2 d25 c94 (by decide +kernel)
  have t3 : a 55 ∈ [0] := remove (a 55) 2 [0,2] d55 b3
  have b4 : a 58 ≠ 1 := exclude [0] (fun u v => edge r101 v u) (a 58) (a 28) 1 d28 c101 (by decide +kernel)
  have t4 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b4
  have b5 : a 60 ≠ 1 := exclude [0] (fun u v => edge r104 v u) (a 60) (a 30) 1 t0 c104 (by decide +kernel)
  have t5 : a 60 ∈ [0] := remove (a 60) 1 [0,1] d60 b5
  have b6 : a 31 ≠ 2 := exclude [0] (edge r105) (a 31) (a 32) 2 d32 c105 (by decide +kernel)
  have t6 : a 31 ∈ [0] := remove (a 31) 2 [0,2] d31 b6
  have b7 : a 37 ≠ 1 := exclude [0] (fun u v => edge r115 v u) (a 37) (a 33) 1 d33 c115 (by decide +kernel)
  have t7 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b7
  have b8 : a 50 ≠ 1 := exclude [0] (fun u v => edge r124 v u) (a 50) (a 35) 1 d35 c124 (by decide +kernel)
  have t8 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b8
  have b9 : a 44 ≠ 1 := exclude [0] (fun u v => edge r136 v u) (a 44) (a 40) 1 d40 c136 (by decide +kernel)
  have t9 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b9
  have b10 : a 49 ≠ 1 := exclude [0] (fun u v => edge r153 v u) (a 49) (a 48) 1 d48 c153 (by decide +kernel)
  have t10 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b10
  have b11 : a 56 ≠ 1 := exclude [0] (fun u v => edge r157 v u) (a 56) (a 49) 1 t10 c157 (by decide +kernel)
  have t11 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b11
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (t11)))))))))))

theorem chunk7 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d5 : a 5 ∈ [0,2])
    (d9 : a 9 ∈ [0,1])
    (d16 : a 16 ∈ [0,1])
    (d32 : a 32 ∈ [0,1])
    (d2 : a 2 ∈ [0,1])
    (d10 : a 10 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (d33 : a 33 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d35 : a 35 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d22 : a 22 ∈ [0,2])
    (d38 : a 38 ∈ [0,1])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 9)=true)
    (c9 : edge r9 (a 1) (a 16)=true)
    (c10 : edge r10 (a 1) (a 32)=true)
    (c11 : edge r11 (a 2) (a 3)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 17)=true)
    (c15 : edge r15 (a 2) (a 33)=true)
    (c16 : edge r16 (a 3) (a 7)=true)
    (c20 : edge r20 (a 4) (a 5)=true)
    (c22 : edge r22 (a 4) (a 12)=true)
    (c24 : edge r24 (a 4) (a 35)=true)
    (c27 : edge r27 (a 5) (a 20)=true)
    (c33 : edge r33 (a 7) (a 22)=true)
    (c34 : edge r34 (a 7) (a 38)=true)
    : a 3 ∈ [1] ∧ a 5 ∈ [2] ∧ a 9 ∈ [1] ∧ a 16 ∈ [1] ∧ a 32 ∈ [1] ∧ a 2 ∈ [1] ∧ a 10 ∈ [1] ∧ a 17 ∈ [2] ∧ a 33 ∈ [1] ∧ a 7 ∈ [2] ∧ a 4 ∈ [1] ∧ a 12 ∈ [1] ∧ a 35 ∈ [1] ∧ a 20 ∈ [2] ∧ a 22 ∈ [2] ∧ a 38 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r6 v u) (a 3) (a 1) 0 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 5 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 5) (a 1) 0 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [2] := remove (a 5) 0 [0,2] d5 b1
  have b2 : a 9 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 9) (a 1) 0 d1 c8 (by decide +kernel)
  have t2 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b2
  have b3 : a 16 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 16) (a 1) 0 d1 c9 (by decide +kernel)
  have t3 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b3
  have b4 : a 32 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 32) (a 1) 0 d1 c10 (by decide +kernel)
  have t4 : a 32 ∈ [1] := remove (a 32) 0 [0,1] d32 b4
  have b5 : a 2 ≠ 0 := exclude [1] (edge r11) (a 2) (a 3) 0 t0 c11 (by decide +kernel)
  have t5 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b5
  have b6 : a 10 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 10) (a 2) 0 t5 c13 (by decide +kernel)
  have t6 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b6
  have b7 : a 17 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 17) (a 2) 0 t5 c14 (by decide +kernel)
  have t7 : a 17 ∈ [2] := remove (a 17) 0 [0,2] d17 b7
  have b8 : a 33 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 33) (a 2) 0 t5 c15 (by decide +kernel)
  have t8 : a 33 ∈ [1] := remove (a 33) 0 [0,1] d33 b8
  have b9 : a 7 ≠ 0 := exclude [1] (fun u v => edge r16 v u) (a 7) (a 3) 0 t0 c16 (by decide +kernel)
  have t9 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b9
  have b10 : a 4 ≠ 0 := exclude [2] (edge r20) (a 4) (a 5) 0 t1 c20 (by decide +kernel)
  have t10 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b10
  have b11 : a 12 ≠ 0 := exclude [1] (fun u v => edge r22 v u) (a 12) (a 4) 0 t10 c22 (by decide +kernel)
  have t11 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b11
  have b12 : a 35 ≠ 0 := exclude [1] (fun u v => edge r24 v u) (a 35) (a 4) 0 t10 c24 (by decide +kernel)
  have t12 : a 35 ∈ [1] := remove (a 35) 0 [0,1] d35 b12
  have b13 : a 20 ≠ 0 := exclude [2] (fun u v => edge r27 v u) (a 20) (a 5) 0 t1 c27 (by decide +kernel)
  have t13 : a 20 ∈ [2] := remove (a 20) 0 [0,2] d20 b13
  have b14 : a 22 ≠ 0 := exclude [2] (fun u v => edge r33 v u) (a 22) (a 7) 0 t9 c33 (by decide +kernel)
  have t14 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b14
  have b15 : a 38 ≠ 0 := exclude [2] (fun u v => edge r34 v u) (a 38) (a 7) 0 t9 c34 (by decide +kernel)
  have t15 : a 38 ∈ [1] := remove (a 38) 0 [0,1] d38 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_235
