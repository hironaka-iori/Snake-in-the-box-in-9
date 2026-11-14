import PartitionData205_233
namespace PartitionCover205_233
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d37 : a 37 ∈ [0,2,3])
    (d36 : a 36 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d44 : a 44 ∈ [0,1])
    (d50 : a 50 ∈ [0,1])
    (d46 : a 46 ∈ [0,1])
    (d57 : a 57 ∈ [0,1])
    (d11 : a 11 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1])
    (c42 : edge r42 (a 11) (a 26)=true)
    (c116 : edge r116 (a 36) (a 37)=true)
    (c135 : edge r135 (a 44) (a 45)=true)
    (c142 : edge r142 (a 46) (a 50)=true)
    (c152 : edge r152 (a 50) (a 57)=true)
    : a 37 ∈ [0,2] ∧ a 45 ∈ [0] ∧ a 50 ∈ [0] ∧ a 57 ∈ [0] ∧ a 11 ∈ [0,1] := by
  have b0 : a 37 ≠ 3 := exclude [0,1] (fun u v => edge r116 v u) (a 37) (a 36) 3 d36 c116 (by decide +kernel)
  have t0 : a 37 ∈ [0,2] := remove (a 37) 3 [0,2,3] d37 b0
  have b1 : a 45 ≠ 1 := exclude [0,1] (fun u v => edge r135 v u) (a 45) (a 44) 1 d44 c135 (by decide +kernel)
  have t1 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b1
  have b2 : a 50 ≠ 1 := exclude [0,1] (fun u v => edge r142 v u) (a 50) (a 46) 1 d46 c142 (by decide +kernel)
  have t2 : a 50 ∈ [0] := remove (a 50) 1 [0,1] d50 b2
  have b3 : a 57 ≠ 1 := exclude [0] (fun u v => edge r152 v u) (a 57) (a 50) 1 t2 c152 (by decide +kernel)
  have t3 : a 57 ∈ [0] := remove (a 57) 1 [0,1] d57 b3
  have b4 : a 11 ≠ 2 := exclude [0,1] (edge r42) (a 11) (a 26) 2 d26 c42 (by decide +kernel)
  have t4 : a 11 ∈ [0,1,3] := remove (a 11) 2 [0,1,2,3] d11 b4
  have b5 : a 11 ≠ 3 := exclude [0,1] (edge r42) (a 11) (a 26) 3 d26 c42 (by decide +kernel)
  have t5 : a 11 ∈ [0,1] := remove (a 11) 3 [0,1,3] t4 b5
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (t5))))

theorem chunk5 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d2 : a 2 ∈ [0,2])
    (d15 : a 15 ∈ [0,2])
    (d30 : a 30 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d4 : a 4 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d18 : a 18 ∈ [0,1])
    (d33 : a 33 ∈ [0,1])
    (d20 : a 20 ∈ [0,2])
    (d35 : a 35 ∈ [0,2])
    (d24 : a 24 ∈ [0,1])
    (c6 : edge r6 (a 1) (a 3)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 14)=true)
    (c9 : edge r9 (a 1) (a 29)=true)
    (c10 : edge r10 (a 2) (a 3)=true)
    (c13 : edge r13 (a 2) (a 15)=true)
    (c14 : edge r14 (a 2) (a 30)=true)
    (c15 : edge r15 (a 3) (a 7)=true)
    (c16 : edge r16 (a 3) (a 10)=true)
    (c19 : edge r19 (a 4) (a 5)=true)
    (c24 : edge r24 (a 5) (a 11)=true)
    (c25 : edge r25 (a 5) (a 18)=true)
    (c26 : edge r26 (a 5) (a 33)=true)
    (c31 : edge r31 (a 7) (a 20)=true)
    (c32 : edge r32 (a 7) (a 35)=true)
    (c40 : edge r40 (a 10) (a 24)=true)
    : a 3 ∈ [0] ∧ a 5 ∈ [0] ∧ a 14 ∈ [0] ∧ a 29 ∈ [0] ∧ a 2 ∈ [0] ∧ a 15 ∈ [0] ∧ a 30 ∈ [0] ∧ a 7 ∈ [0] ∧ a 10 ∈ [0] ∧ a 4 ∈ [0] ∧ a 11 ∈ [0] ∧ a 18 ∈ [0] ∧ a 33 ∈ [0] ∧ a 20 ∈ [0] ∧ a 35 ∈ [0] ∧ a 24 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r6 v u) (a 3) (a 1) 1 d1 c6 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 5 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 5) (a 1) 1 d1 c7 (by decide +kernel)
  have t1 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b1
  have b2 : a 14 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 14) (a 1) 1 d1 c8 (by decide +kernel)
  have t2 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b2
  have b3 : a 29 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 29) (a 1) 1 d1 c9 (by decide +kernel)
  have t3 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b3
  have b4 : a 2 ≠ 2 := exclude [0] (edge r10) (a 2) (a 3) 2 t0 c10 (by decide +kernel)
  have t4 : a 2 ∈ [0] := remove (a 2) 2 [0,2] d2 b4
  have b5 : a 15 ≠ 2 := exclude [0] (fun u v => edge r13 v u) (a 15) (a 2) 2 t4 c13 (by decide +kernel)
  have t5 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b5
  have b6 : a 30 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 30) (a 2) 1 t4 c14 (by decide +kernel)
  have t6 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b6
  have b7 : a 7 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 7) (a 3) 2 t0 c15 (by decide +kernel)
  have t7 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b7
  have b8 : a 10 ≠ 2 := exclude [0] (fun u v => edge r16 v u) (a 10) (a 3) 2 t0 c16 (by decide +kernel)
  have t8 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b8
  have b9 : a 4 ≠ 2 := exclude [0] (edge r19) (a 4) (a 5) 2 t1 c19 (by decide +kernel)
  have t9 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b9
  have b10 : a 11 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 11) (a 5) 1 t1 c24 (by decide +kernel)
  have t10 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b10
  have b11 : a 18 ≠ 1 := exclude [0] (fun u v => edge r25 v u) (a 18) (a 5) 1 t1 c25 (by decide +kernel)
  have t11 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b11
  have b12 : a 33 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 33) (a 5) 1 t1 c26 (by decide +kernel)
  have t12 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b12
  have b13 : a 20 ≠ 2 := exclude [0] (fun u v => edge r31 v u) (a 20) (a 7) 2 t7 c31 (by decide +kernel)
  have t13 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b13
  have b14 : a 35 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 35) (a 7) 2 t7 c32 (by decide +kernel)
  have t14 : a 35 ∈ [0] := remove (a 35) 2 [0,2] d35 b14
  have b15 : a 24 ≠ 1 := exclude [0] (fun u v => edge r40 v u) (a 24) (a 10) 1 t8 c40 (by decide +kernel)
  have t15 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d41 : a 41 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d21 : a 21 ∈ [0,2])
    (d44 : a 44 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d19 : a 19 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d46 : a 46 ∈ [0,1])
    (d49 : a 49 ∈ [0,2])
    (d18 : a 18 ∈ [0])
    (d27 : a 27 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d25 : a 25 ∈ [0,2])
    (d54 : a 54 ∈ [0,1])
    (d24 : a 24 ∈ [0])
    (d55 : a 55 ∈ [0,1])
    (d56 : a 56 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (d29 : a 29 ∈ [0])
    (c42 : edge r42 (a 11) (a 26)=true)
    (c43 : edge r43 (a 11) (a 41)=true)
    (c46 : edge r46 (a 13) (a 14)=true)
    (c49 : edge r49 (a 13) (a 21)=true)
    (c50 : edge r50 (a 13) (a 44)=true)
    (c53 : edge r53 (a 14) (a 22)=true)
    (c56 : edge r56 (a 15) (a 19)=true)
    (c58 : edge r58 (a 15) (a 46)=true)
    (c68 : edge r68 (a 18) (a 49)=true)
    (c70 : edge r70 (a 19) (a 27)=true)
    (c72 : edge r72 (a 20) (a 51)=true)
    (c75 : edge r75 (a 21) (a 25)=true)
    (c82 : edge r82 (a 24) (a 54)=true)
    (c85 : edge r85 (a 25) (a 55)=true)
    (c86 : edge r86 (a 26) (a 56)=true)
    (c88 : edge r88 (a 28) (a 29)=true)
    : a 26 ∈ [0] ∧ a 41 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 44 ∈ [0] ∧ a 22 ∈ [0] ∧ a 19 ∈ [0] ∧ a 46 ∈ [0] ∧ a 49 ∈ [0] ∧ a 27 ∈ [0] ∧ a 51 ∈ [0] ∧ a 25 ∈ [0] ∧ a 54 ∈ [0] ∧ a 55 ∈ [0] ∧ a 56 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 26 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 26) (a 11) 1 d11 c42 (by decide +kernel)
  have t0 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b0
  have b1 : a 41 ≠ 1 := exclude [0] (fun u v => edge r43 v u) (a 41) (a 11) 1 d11 c43 (by decide +kernel)
  have t1 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b1
  have b2 : a 13 ≠ 2 := exclude [0] (edge r46) (a 13) (a 14) 2 d14 c46 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b2
  have b3 : a 21 ≠ 2 := exclude [0] (fun u v => edge r49 v u) (a 21) (a 13) 2 t2 c49 (by decide +kernel)
  have t3 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b3
  have b4 : a 44 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 44) (a 13) 1 t2 c50 (by decide +kernel)
  have t4 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b4
  have b5 : a 22 ≠ 2 := exclude [0] (fun u v => edge r53 v u) (a 22) (a 14) 2 d14 c53 (by decide +kernel)
  have t5 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b5
  have b6 : a 19 ≠ 1 := exclude [0] (fun u v => edge r56 v u) (a 19) (a 15) 1 d15 c56 (by decide +kernel)
  have t6 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b6
  have b7 : a 46 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 46) (a 15) 1 d15 c58 (by decide +kernel)
  have t7 : a 46 ∈ [0] := remove (a 46) 1 [0,1] d46 b7
  have b8 : a 49 ≠ 2 := exclude [0] (fun u v => edge r68 v u) (a 49) (a 18) 2 d18 c68 (by decide +kernel)
  have t8 : a 49 ∈ [0] := remove (a 49) 2 [0,2] d49 b8
  have b9 : a 27 ≠ 1 := exclude [0] (fun u v => edge r70 v u) (a 27) (a 19) 1 t6 c70 (by decide +kernel)
  have t9 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b9
  have b10 : a 51 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 51) (a 20) 1 d20 c72 (by decide +kernel)
  have t10 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b10
  have b11 : a 25 ≠ 2 := exclude [0] (fun u v => edge r75 v u) (a 25) (a 21) 2 t3 c75 (by decide +kernel)
  have t11 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b11
  have b12 : a 54 ≠ 1 := exclude [0] (fun u v => edge r82 v u) (a 54) (a 24) 1 d24 c82 (by decide +kernel)
  have t12 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b12
  have b13 : a 55 ≠ 1 := exclude [0] (fun u v => edge r85 v u) (a 55) (a 25) 1 t11 c85 (by decide +kernel)
  have t13 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b13
  have b14 : a 56 ≠ 1 := exclude [0] (fun u v => edge r86 v u) (a 56) (a 26) 1 t0 c86 (by decide +kernel)
  have t14 : a 56 ∈ [0] := remove (a 56) 1 [0,1] d56 b14
  have b15 : a 28 ≠ 1 := exclude [0] (edge r88) (a 28) (a 29) 1 d29 c88 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk7 (a : Nat → Nat)
    (d36 : a 36 ∈ [0,1])
    (d28 : a 28 ∈ [0])
    (d37 : a 37 ∈ [0,2])
    (d29 : a 29 ∈ [0])
    (d34 : a 34 ∈ [0,1])
    (d30 : a 30 ∈ [0])
    (d38 : a 38 ∈ [0,1])
    (d42 : a 42 ∈ [0,1])
    (d43 : a 43 ∈ [0,2])
    (d35 : a 35 ∈ [0])
    (d58 : a 58 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d44 : a 44 ∈ [0])
    (d47 : a 47 ∈ [0,1])
    (d46 : a 46 ∈ [0])
    (d8 : a 8 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d12 : a 12 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (c34 : edge r34 (a 8) (a 21)=true)
    (c44 : edge r44 (a 12) (a 27)=true)
    (c91 : edge r91 (a 28) (a 36)=true)
    (c95 : edge r95 (a 29) (a 37)=true)
    (c98 : edge r98 (a 30) (a 34)=true)
    (c99 : edge r99 (a 30) (a 38)=true)
    (c112 : edge r112 (a 34) (a 42)=true)
    (c114 : edge r114 (a 35) (a 43)=true)
    (c134 : edge r134 (a 43) (a 58)=true)
    (c137 : edge r137 (a 44) (a 48)=true)
    (c141 : edge r141 (a 46) (a 47)=true)
    : a 36 ∈ [0] ∧ a 37 ∈ [0] ∧ a 34 ∈ [0] ∧ a 38 ∈ [0] ∧ a 42 ∈ [0] ∧ a 43 ∈ [0] ∧ a 58 ∈ [0] ∧ a 48 ∈ [0] ∧ a 47 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] := by
  have b0 : a 36 ≠ 1 := exclude [0] (fun u v => edge r91 v u) (a 36) (a 28) 1 d28 c91 (by decide +kernel)
  have t0 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b0
  have b1 : a 37 ≠ 2 := exclude [0] (fun u v => edge r95 v u) (a 37) (a 29) 2 d29 c95 (by decide +kernel)
  have t1 : a 37 ∈ [0] := remove (a 37) 2 [0,2] d37 b1
  have b2 : a 34 ≠ 1 := exclude [0] (fun u v => edge r98 v u) (a 34) (a 30) 1 d30 c98 (by decide +kernel)
  have t2 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b2
  have b3 : a 38 ≠ 1 := exclude [0] (fun u v => edge r99 v u) (a 38) (a 30) 1 d30 c99 (by decide +kernel)
  have t3 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b3
  have b4 : a 42 ≠ 1 := exclude [0] (fun u v => edge r112 v u) (a 42) (a 34) 1 t2 c112 (by decide +kernel)
  have t4 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b4
  have b5 : a 43 ≠ 2 := exclude [0] (fun u v => edge r114 v u) (a 43) (a 35) 2 d35 c114 (by decide +kernel)
  have t5 : a 43 ∈ [0] := remove (a 43) 2 [0,2] d43 b5
  have b6 : a 58 ≠ 1 := exclude [0] (fun u v => edge r134 v u) (a 58) (a 43) 1 t5 c134 (by decide +kernel)
  have t6 : a 58 ∈ [0] := remove (a 58) 1 [0,1] d58 b6
  have b7 : a 48 ≠ 1 := exclude [0] (fun u v => edge r137 v u) (a 48) (a 44) 1 d44 c137 (by decide +kernel)
  have t7 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b7
  have b8 : a 47 ≠ 1 := exclude [0] (fun u v => edge r141 v u) (a 47) (a 46) 1 d46 c141 (by decide +kernel)
  have t8 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b8
  have b9 : a 8 ≠ 1 := exclude [0] (edge r34) (a 8) (a 21) 1 d21 c34 (by decide +kernel)
  have t9 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b9
  have b10 : a 12 ≠ 1 := exclude [0] (edge r44) (a 12) (a 27) 1 d27 c44 (by decide +kernel)
  have t10 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b10
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (t10))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_233
