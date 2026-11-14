import PartitionData205_234
namespace PartitionCover205_234
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d8 : a 8 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1,2,3])
    (d1 : a 1 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,2,3])
    (d31 : a 31 ∈ [0,1,2,3])
    (d7 : a 7 ∈ [0,1,2,3])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 14)=true)
    (c5 : edge r5 (a 0) (a 29)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c11 : edge r11 (a 2) (a 6)=true)
    (c12 : edge r12 (a 2) (a 16)=true)
    (c13 : edge r13 (a 2) (a 31)=true)
    (c23 : edge r23 (a 5) (a 7)=true)
    : a 2 ∈ [0,2] ∧ a 8 ∈ [0,2] ∧ a 14 ∈ [0,2] ∧ a 29 ∈ [0,2] ∧ a 5 ∈ [0,1] ∧ a 6 ∈ [0] ∧ a 16 ∈ [0,2] ∧ a 31 ∈ [0,1] ∧ a 7 ∈ [0,2,3] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0,2,3] := remove (a 2) 1 [0,1,2,3] d2 b0
  have b1 : a 2 ≠ 3 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 3 d0 c1 (by decide +kernel)
  have t1 : a 2 ∈ [0,2] := remove (a 2) 3 [0,2,3] t0 b1
  have b2 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0,2,3] := remove (a 8) 1 [0,1,2,3] d8 b2
  have b3 : a 8 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 3 d0 c3 (by decide +kernel)
  have t3 : a 8 ∈ [0,2] := remove (a 8) 3 [0,2,3] t2 b3
  have b4 : a 14 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 14) (a 0) 1 d0 c4 (by decide +kernel)
  have t4 : a 14 ∈ [0,2,3] := remove (a 14) 1 [0,1,2,3] d14 b4
  have b5 : a 14 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 14) (a 0) 3 d0 c4 (by decide +kernel)
  have t5 : a 14 ∈ [0,2] := remove (a 14) 3 [0,2,3] t4 b5
  have b6 : a 29 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 29) (a 0) 1 d0 c5 (by decide +kernel)
  have t6 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b6
  have b7 : a 29 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 29) (a 0) 3 d0 c5 (by decide +kernel)
  have t7 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t6 b7
  have b8 : a 5 ≠ 2 := exclude [0,1] (fun u v => edge r7 v u) (a 5) (a 1) 2 d1 c7 (by decide +kernel)
  have t8 : a 5 ∈ [0,1,3] := remove (a 5) 2 [0,1,2,3] d5 b8
  have b9 : a 5 ≠ 3 := exclude [0,1] (fun u v => edge r7 v u) (a 5) (a 1) 3 d1 c7 (by decide +kernel)
  have t9 : a 5 ∈ [0,1] := remove (a 5) 3 [0,1,3] t8 b9
  have b10 : a 6 ≠ 1 := exclude [0,2] (fun u v => edge r11 v u) (a 6) (a 2) 1 t1 c11 (by decide +kernel)
  have t10 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b10
  have b11 : a 16 ≠ 1 := exclude [0,2] (fun u v => edge r12 v u) (a 16) (a 2) 1 t1 c12 (by decide +kernel)
  have t11 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b11
  have b12 : a 16 ≠ 3 := exclude [0,2] (fun u v => edge r12 v u) (a 16) (a 2) 3 t1 c12 (by decide +kernel)
  have t12 : a 16 ∈ [0,2] := remove (a 16) 3 [0,2,3] t11 b12
  have b13 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r13 v u) (a 31) (a 2) 2 t1 c13 (by decide +kernel)
  have t13 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b13
  have b14 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r13 v u) (a 31) (a 2) 3 t1 c13 (by decide +kernel)
  have t14 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t13 b14
  have b15 : a 7 ≠ 1 := exclude [0,1] (fun u v => edge r23 v u) (a 7) (a 5) 1 t9 c23 (by decide +kernel)
  have t15 : a 7 ∈ [0,2,3] := remove (a 7) 1 [0,1,2,3] d7 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))))))

theorem chunk1 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,2,3])
    (d5 : a 5 ∈ [0,1])
    (d11 : a 11 ∈ [0,1])
    (d19 : a 19 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0,1])
    (d12 : a 12 ∈ [0,1,2,3])
    (d6 : a 6 ∈ [0])
    (d13 : a 13 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3])
    (d36 : a 36 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,1,2,3])
    (c23 : edge r23 (a 5) (a 7)=true)
    (c24 : edge r24 (a 5) (a 11)=true)
    (c25 : edge r25 (a 5) (a 19)=true)
    (c26 : edge r26 (a 5) (a 34)=true)
    (c28 : edge r28 (a 6) (a 12)=true)
    (c31 : edge r31 (a 7) (a 13)=true)
    (c32 : edge r32 (a 7) (a 21)=true)
    (c33 : edge r33 (a 7) (a 36)=true)
    (c36 : edge r36 (a 9) (a 13)=true)
    (c37 : edge r37 (a 9) (a 25)=true)
    : a 7 ∈ [0,2] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0,1] ∧ a 34 ∈ [0] ∧ a 12 ∈ [0,1] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0,2] ∧ a 36 ∈ [0,2] ∧ a 9 ∈ [0,2] ∧ a 25 ∈ [0,1] := by
  have b0 : a 7 ≠ 3 := exclude [0,1] (fun u v => edge r23 v u) (a 7) (a 5) 3 d5 c23 (by decide +kernel)
  have t0 : a 7 ∈ [0,2] := remove (a 7) 3 [0,2,3] d7 b0
  have b1 : a 11 ≠ 1 := exclude [0,1] (fun u v => edge r24 v u) (a 11) (a 5) 1 d5 c24 (by decide +kernel)
  have t1 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b1
  have b2 : a 19 ≠ 2 := exclude [0,1] (fun u v => edge r25 v u) (a 19) (a 5) 2 d5 c25 (by decide +kernel)
  have t2 : a 19 ∈ [0,1,3] := remove (a 19) 2 [0,1,2,3] d19 b2
  have b3 : a 19 ≠ 3 := exclude [0,1] (fun u v => edge r25 v u) (a 19) (a 5) 3 d5 c25 (by decide +kernel)
  have t3 : a 19 ∈ [0,1] := remove (a 19) 3 [0,1,3] t2 b3
  have b4 : a 34 ≠ 1 := exclude [0,1] (fun u v => edge r26 v u) (a 34) (a 5) 1 d5 c26 (by decide +kernel)
  have t4 : a 34 ∈ [0] := remove (a 34) 1 [0,1] d34 b4
  have b5 : a 12 ≠ 2 := exclude [0] (fun u v => edge r28 v u) (a 12) (a 6) 2 d6 c28 (by decide +kernel)
  have t5 : a 12 ∈ [0,1,3] := remove (a 12) 2 [0,1,2,3] d12 b5
  have b6 : a 12 ≠ 3 := exclude [0] (fun u v => edge r28 v u) (a 12) (a 6) 3 d6 c28 (by decide +kernel)
  have t6 : a 12 ∈ [0,1] := remove (a 12) 3 [0,1,3] t5 b6
  have b7 : a 13 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 13) (a 7) 1 t0 c31 (by decide +kernel)
  have t7 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b7
  have b8 : a 21 ≠ 1 := exclude [0,2] (fun u v => edge r32 v u) (a 21) (a 7) 1 t0 c32 (by decide +kernel)
  have t8 : a 21 ∈ [0,2,3] := remove (a 21) 1 [0,1,2,3] d21 b8
  have b9 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r32 v u) (a 21) (a 7) 3 t0 c32 (by decide +kernel)
  have t9 : a 21 ∈ [0,2] := remove (a 21) 3 [0,2,3] t8 b9
  have b10 : a 36 ≠ 1 := exclude [0,2] (fun u v => edge r33 v u) (a 36) (a 7) 1 t0 c33 (by decide +kernel)
  have t10 : a 36 ∈ [0,2,3] := remove (a 36) 1 [0,1,2,3] d36 b10
  have b11 : a 36 ≠ 3 := exclude [0,2] (fun u v => edge r33 v u) (a 36) (a 7) 3 t0 c33 (by decide +kernel)
  have t11 : a 36 ∈ [0,2] := remove (a 36) 3 [0,2,3] t10 b11
  have b12 : a 9 ≠ 1 := exclude [0] (edge r36) (a 9) (a 13) 1 t7 c36 (by decide +kernel)
  have t12 : a 9 ∈ [0,2,3] := remove (a 9) 1 [0,1,2,3] d9 b12
  have b13 : a 9 ≠ 3 := exclude [0] (edge r36) (a 9) (a 13) 3 t7 c36 (by decide +kernel)
  have t13 : a 9 ∈ [0,2] := remove (a 9) 3 [0,2,3] t12 b13
  have b14 : a 25 ≠ 2 := exclude [0,2] (fun u v => edge r37 v u) (a 25) (a 9) 2 t13 c37 (by decide +kernel)
  have t14 : a 25 ∈ [0,1,3] := remove (a 25) 2 [0,1,2,3] d25 b14
  have b15 : a 25 ≠ 3 := exclude [0,2] (fun u v => edge r37 v u) (a 25) (a 9) 3 t13 c37 (by decide +kernel)
  have t15 : a 25 ∈ [0,1] := remove (a 25) 3 [0,1,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t13 (t15)))))))))

theorem chunk2 (a : Nat → Nat)
    (d39 : a 39 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d40 : a 40 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0])
    (d42 : a 42 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d18 : a 18 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d43 : a 43 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1])
    (d16 : a 16 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2,3])
    (d45 : a 45 ∈ [0,1,2,3])
    (d26 : a 26 ∈ [0,1])
    (d47 : a 47 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1])
    (d49 : a 49 ∈ [0,1,2,3])
    (d21 : a 21 ∈ [0,2])
    (c38 : edge r38 (a 9) (a 39)=true)
    (c44 : edge r44 (a 11) (a 40)=true)
    (c48 : edge r48 (a 13) (a 42)=true)
    (c51 : edge r51 (a 14) (a 18)=true)
    (c53 : edge r53 (a 14) (a 43)=true)
    (c58 : edge r58 (a 16) (a 17)=true)
    (c60 : edge r60 (a 16) (a 24)=true)
    (c61 : edge r61 (a 16) (a 45)=true)
    (c67 : edge r67 (a 18) (a 26)=true)
    (c70 : edge r70 (a 19) (a 47)=true)
    (c74 : edge r74 (a 21) (a 49)=true)
    : a 39 ∈ [0] ∧ a 40 ∈ [0,2] ∧ a 42 ∈ [0] ∧ a 18 ∈ [0] ∧ a 43 ∈ [0,2] ∧ a 17 ∈ [0] ∧ a 24 ∈ [0,2] ∧ a 45 ∈ [0,1] ∧ a 26 ∈ [0] ∧ a 47 ∈ [0,1] ∧ a 49 ∈ [0,1,3] := by
  have b0 : a 39 ≠ 1 := exclude [0,2] (fun u v => edge r38 v u) (a 39) (a 9) 1 d9 c38 (by decide +kernel)
  have t0 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b0
  have b1 : a 40 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 40) (a 11) 1 d11 c44 (by decide +kernel)
  have t1 : a 40 ∈ [0,2,3] := remove (a 40) 1 [0,1,2,3] d40 b1
  have b2 : a 40 ≠ 3 := exclude [0] (fun u v => edge r44 v u) (a 40) (a 11) 3 d11 c44 (by decide +kernel)
  have t2 : a 40 ∈ [0,2] := remove (a 40) 3 [0,2,3] t1 b2
  have b3 : a 42 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 42) (a 13) 1 d13 c48 (by decide +kernel)
  have t3 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b3
  have b4 : a 18 ≠ 1 := exclude [0,2] (fun u v => edge r51 v u) (a 18) (a 14) 1 d14 c51 (by decide +kernel)
  have t4 : a 18 ∈ [0] := remove (a 18) 1 [0,1] d18 b4
  have b5 : a 43 ≠ 1 := exclude [0,2] (fun u v => edge r53 v u) (a 43) (a 14) 1 d14 c53 (by decide +kernel)
  have t5 : a 43 ∈ [0,2,3] := remove (a 43) 1 [0,1,2,3] d43 b5
  have b6 : a 43 ≠ 3 := exclude [0,2] (fun u v => edge r53 v u) (a 43) (a 14) 3 d14 c53 (by decide +kernel)
  have t6 : a 43 ∈ [0,2] := remove (a 43) 3 [0,2,3] t5 b6
  have b7 : a 17 ≠ 1 := exclude [0,2] (fun u v => edge r58 v u) (a 17) (a 16) 1 d16 c58 (by decide +kernel)
  have t7 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b7
  have b8 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r60 v u) (a 24) (a 16) 1 d16 c60 (by decide +kernel)
  have t8 : a 24 ∈ [0,2,3] := remove (a 24) 1 [0,1,2,3] d24 b8
  have b9 : a 24 ≠ 3 := exclude [0,2] (fun u v => edge r60 v u) (a 24) (a 16) 3 d16 c60 (by decide +kernel)
  have t9 : a 24 ∈ [0,2] := remove (a 24) 3 [0,2,3] t8 b9
  have b10 : a 45 ≠ 2 := exclude [0,2] (fun u v => edge r61 v u) (a 45) (a 16) 2 d16 c61 (by decide +kernel)
  have t10 : a 45 ∈ [0,1,3] := remove (a 45) 2 [0,1,2,3] d45 b10
  have b11 : a 45 ≠ 3 := exclude [0,2] (fun u v => edge r61 v u) (a 45) (a 16) 3 d16 c61 (by decide +kernel)
  have t11 : a 45 ∈ [0,1] := remove (a 45) 3 [0,1,3] t10 b11
  have b12 : a 26 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 26) (a 18) 1 t4 c67 (by decide +kernel)
  have t12 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b12
  have b13 : a 47 ≠ 2 := exclude [0,1] (fun u v => edge r70 v u) (a 47) (a 19) 2 d19 c70 (by decide +kernel)
  have t13 : a 47 ∈ [0,1,3] := remove (a 47) 2 [0,1,2,3] d47 b13
  have b14 : a 47 ≠ 3 := exclude [0,1] (fun u v => edge r70 v u) (a 47) (a 19) 3 d19 c70 (by decide +kernel)
  have t14 : a 47 ∈ [0,1] := remove (a 47) 3 [0,1,3] t13 b14
  have b15 : a 49 ≠ 2 := exclude [0,2] (fun u v => edge r74 v u) (a 49) (a 21) 2 d21 c74 (by decide +kernel)
  have t15 : a 49 ∈ [0,1,3] := remove (a 49) 2 [0,1,2,3] d49 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t14 (t15))))))))))

theorem chunk3 (a : Nat → Nat)
    (d49 : a 49 ∈ [0,1,3])
    (d21 : a 21 ∈ [0,2])
    (d23 : a 23 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,1])
    (d51 : a 51 ∈ [0,1])
    (d53 : a 53 ∈ [0,1])
    (d26 : a 26 ∈ [0])
    (d33 : a 33 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,2])
    (d32 : a 32 ∈ [0,1])
    (d31 : a 31 ∈ [0,1])
    (d38 : a 38 ∈ [0,1,2,3])
    (d37 : a 37 ∈ [0,1,2,3])
    (d39 : a 39 ∈ [0])
    (d44 : a 44 ∈ [0,1])
    (d43 : a 43 ∈ [0,2])
    (d48 : a 48 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d55 : a 55 ∈ [0,1])
    (c74 : edge r74 (a 21) (a 49)=true)
    (c79 : edge r79 (a 23) (a 25)=true)
    (c81 : edge r81 (a 23) (a 51)=true)
    (c87 : edge r87 (a 26) (a 53)=true)
    (c92 : edge r92 (a 29) (a 33)=true)
    (c98 : edge r98 (a 31) (a 32)=true)
    (c100 : edge r100 (a 31) (a 38)=true)
    (c115 : edge r115 (a 37) (a 39)=true)
    (c127 : edge r127 (a 43) (a 44)=true)
    (c134 : edge r134 (a 45) (a 48)=true)
    (c140 : edge r140 (a 48) (a 55)=true)
    : a 49 ∈ [0,1] ∧ a 23 ∈ [0,1] ∧ a 51 ∈ [0] ∧ a 53 ∈ [0] ∧ a 33 ∈ [0,2] ∧ a 32 ∈ [0] ∧ a 38 ∈ [0,1] ∧ a 37 ∈ [0,1] ∧ a 44 ∈ [0] ∧ a 48 ∈ [0] ∧ a 55 ∈ [0] := by
  have b0 : a 49 ≠ 3 := exclude [0,2] (fun u v => edge r74 v u) (a 49) (a 21) 3 d21 c74 (by decide +kernel)
  have t0 : a 49 ∈ [0,1] := remove (a 49) 3 [0,1,3] d49 b0
  have b1 : a 23 ≠ 2 := exclude [0,1] (edge r79) (a 23) (a 25) 2 d25 c79 (by decide +kernel)
  have t1 : a 23 ∈ [0,1,3] := remove (a 23) 2 [0,1,2,3] d23 b1
  have b2 : a 23 ≠ 3 := exclude [0,1] (edge r79) (a 23) (a 25) 3 d25 c79 (by decide +kernel)
  have t2 : a 23 ∈ [0,1] := remove (a 23) 3 [0,1,3] t1 b2
  have b3 : a 51 ≠ 1 := exclude [0,1] (fun u v => edge r81 v u) (a 51) (a 23) 1 t2 c81 (by decide +kernel)
  have t3 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b3
  have b4 : a 53 ≠ 1 := exclude [0] (fun u v => edge r87 v u) (a 53) (a 26) 1 d26 c87 (by decide +kernel)
  have t4 : a 53 ∈ [0] := remove (a 53) 1 [0,1] d53 b4
  have b5 : a 33 ≠ 1 := exclude [0,2] (fun u v => edge r92 v u) (a 33) (a 29) 1 d29 c92 (by decide +kernel)
  have t5 : a 33 ∈ [0,2,3] := remove (a 33) 1 [0,1,2,3] d33 b5
  have b6 : a 33 ≠ 3 := exclude [0,2] (fun u v => edge r92 v u) (a 33) (a 29) 3 d29 c92 (by decide +kernel)
  have t6 : a 33 ∈ [0,2] := remove (a 33) 3 [0,2,3] t5 b6
  have b7 : a 32 ≠ 1 := exclude [0,1] (fun u v => edge r98 v u) (a 32) (a 31) 1 d31 c98 (by decide +kernel)
  have t7 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b7
  have b8 : a 38 ≠ 2 := exclude [0,1] (fun u v => edge r100 v u) (a 38) (a 31) 2 d31 c100 (by decide +kernel)
  have t8 : a 38 ∈ [0,1,3] := remove (a 38) 2 [0,1,2,3] d38 b8
  have b9 : a 38 ≠ 3 := exclude [0,1] (fun u v => edge r100 v u) (a 38) (a 31) 3 d31 c100 (by decide +kernel)
  have t9 : a 38 ∈ [0,1] := remove (a 38) 3 [0,1,3] t8 b9
  have b10 : a 37 ≠ 2 := exclude [0] (edge r115) (a 37) (a 39) 2 d39 c115 (by decide +kernel)
  have t10 : a 37 ∈ [0,1,3] := remove (a 37) 2 [0,1,2,3] d37 b10
  have b11 : a 37 ≠ 3 := exclude [0] (edge r115) (a 37) (a 39) 3 d39 c115 (by decide +kernel)
  have t11 : a 37 ∈ [0,1] := remove (a 37) 3 [0,1,3] t10 b11
  have b12 : a 44 ≠ 1 := exclude [0,2] (fun u v => edge r127 v u) (a 44) (a 43) 1 d43 c127 (by decide +kernel)
  have t12 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b12
  have b13 : a 48 ≠ 1 := exclude [0,1] (fun u v => edge r134 v u) (a 48) (a 45) 1 d45 c134 (by decide +kernel)
  have t13 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b13
  have b14 : a 55 ≠ 1 := exclude [0] (fun u v => edge r140 v u) (a 55) (a 48) 1 t13 c140 (by decide +kernel)
  have t14 : a 55 ∈ [0] := remove (a 55) 1 [0,1] d55 b14
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t13 (t14))))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_234
