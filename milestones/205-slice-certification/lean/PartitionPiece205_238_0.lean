import PartitionData205_238
namespace PartitionCover205_238
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d7 : a 7 ∈ [0,1,2,3])
    (d0 : a 0 ∈ [0])
    (d14 : a 14 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1,2,3])
    (d3 : a 3 ∈ [0,1])
    (d17 : a 17 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d22 : a 22 ∈ [0,1,2,3])
    (d36 : a 36 ∈ [0,1,2,3])
    (c3 : edge r3 (a 0) (a 7)=true)
    (c4 : edge r4 (a 0) (a 14)=true)
    (c5 : edge r5 (a 0) (a 29)=true)
    (c15 : edge r15 (a 3) (a 9)=true)
    (c16 : edge r16 (a 3) (a 17)=true)
    (c17 : edge r17 (a 3) (a 32)=true)
    (c28 : edge r28 (a 7) (a 8)=true)
    (c30 : edge r30 (a 7) (a 22)=true)
    (c31 : edge r31 (a 7) (a 36)=true)
    : a 7 ∈ [0,1] ∧ a 14 ∈ [0,1] ∧ a 29 ∈ [0,2] ∧ a 9 ∈ [0,1] ∧ a 17 ∈ [0,1] ∧ a 32 ∈ [0] ∧ a 8 ∈ [0] ∧ a 22 ∈ [0,2] ∧ a 36 ∈ [0,2] := by
  have b0 : a 7 ≠ 2 := exclude [0] (fun u v => edge r3 v u) (a 7) (a 0) 2 d0 c3 (by decide +kernel)
  have t0 : a 7 ∈ [0,1,3] := remove (a 7) 2 [0,1,2,3] d7 b0
  have b1 : a 7 ≠ 3 := exclude [0] (fun u v => edge r3 v u) (a 7) (a 0) 3 d0 c3 (by decide +kernel)
  have t1 : a 7 ∈ [0,1] := remove (a 7) 3 [0,1,3] t0 b1
  have b2 : a 14 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 14) (a 0) 2 d0 c4 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,3] := remove (a 14) 2 [0,1,2,3] d14 b2
  have b3 : a 14 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 14) (a 0) 3 d0 c4 (by decide +kernel)
  have t3 : a 14 ∈ [0,1] := remove (a 14) 3 [0,1,3] t2 b3
  have b4 : a 29 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 29) (a 0) 1 d0 c5 (by decide +kernel)
  have t4 : a 29 ∈ [0,2,3] := remove (a 29) 1 [0,1,2,3] d29 b4
  have b5 : a 29 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 29) (a 0) 3 d0 c5 (by decide +kernel)
  have t5 : a 29 ∈ [0,2] := remove (a 29) 3 [0,2,3] t4 b5
  have b6 : a 9 ≠ 2 := exclude [0,1] (fun u v => edge r15 v u) (a 9) (a 3) 2 d3 c15 (by decide +kernel)
  have t6 : a 9 ∈ [0,1,3] := remove (a 9) 2 [0,1,2,3] d9 b6
  have b7 : a 9 ≠ 3 := exclude [0,1] (fun u v => edge r15 v u) (a 9) (a 3) 3 d3 c15 (by decide +kernel)
  have t7 : a 9 ∈ [0,1] := remove (a 9) 3 [0,1,3] t6 b7
  have b8 : a 17 ≠ 2 := exclude [0,1] (fun u v => edge r16 v u) (a 17) (a 3) 2 d3 c16 (by decide +kernel)
  have t8 : a 17 ∈ [0,1,3] := remove (a 17) 2 [0,1,2,3] d17 b8
  have b9 : a 17 ≠ 3 := exclude [0,1] (fun u v => edge r16 v u) (a 17) (a 3) 3 d3 c16 (by decide +kernel)
  have t9 : a 17 ∈ [0,1] := remove (a 17) 3 [0,1,3] t8 b9
  have b10 : a 32 ≠ 1 := exclude [0,1] (fun u v => edge r17 v u) (a 32) (a 3) 1 d3 c17 (by decide +kernel)
  have t10 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b10
  have b11 : a 8 ≠ 1 := exclude [0,1] (fun u v => edge r28 v u) (a 8) (a 7) 1 t1 c28 (by decide +kernel)
  have t11 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b11
  have b12 : a 22 ≠ 1 := exclude [0,1] (fun u v => edge r30 v u) (a 22) (a 7) 1 t1 c30 (by decide +kernel)
  have t12 : a 22 ∈ [0,2,3] := remove (a 22) 1 [0,1,2,3] d22 b12
  have b13 : a 22 ≠ 3 := exclude [0,1] (fun u v => edge r30 v u) (a 22) (a 7) 3 t1 c30 (by decide +kernel)
  have t13 : a 22 ∈ [0,2] := remove (a 22) 3 [0,2,3] t12 b13
  have b14 : a 36 ≠ 1 := exclude [0,1] (fun u v => edge r31 v u) (a 36) (a 7) 1 t1 c31 (by decide +kernel)
  have t14 : a 36 ∈ [0,2,3] := remove (a 36) 1 [0,1,2,3] d36 b14
  have b15 : a 36 ≠ 3 := exclude [0,1] (fun u v => edge r31 v u) (a 36) (a 7) 3 t1 c31 (by decide +kernel)
  have t15 : a 36 ∈ [0,2] := remove (a 36) 3 [0,2,3] t14 b15
  exact And.intro t1 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (t15))))))))

theorem chunk1 (a : Nat → Nat)
    (d12 : a 12 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d25 : a 25 ∈ [0,1,2,3])
    (d9 : a 9 ∈ [0,1])
    (d39 : a 39 ∈ [0,1,2,3])
    (d42 : a 42 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d18 : a 18 ∈ [0,1,2,3])
    (d44 : a 44 ∈ [0,1,2,3])
    (d20 : a 20 ∈ [0,1])
    (d21 : a 21 ∈ [0,1,2,3])
    (d17 : a 17 ∈ [0,1])
    (d47 : a 47 ∈ [0,1,2,3])
    (c33 : edge r33 (a 8) (a 12)=true)
    (c37 : edge r37 (a 9) (a 25)=true)
    (c38 : edge r38 (a 9) (a 39)=true)
    (c48 : edge r48 (a 12) (a 42)=true)
    (c51 : edge r51 (a 14) (a 16)=true)
    (c52 : edge r52 (a 14) (a 18)=true)
    (c54 : edge r54 (a 14) (a 44)=true)
    (c60 : edge r60 (a 16) (a 20)=true)
    (c63 : edge r63 (a 17) (a 21)=true)
    (c65 : edge r65 (a 17) (a 47)=true)
    : a 12 ∈ [0] ∧ a 25 ∈ [0,2] ∧ a 39 ∈ [0,1] ∧ a 42 ∈ [0,1] ∧ a 16 ∈ [0] ∧ a 18 ∈ [0,2] ∧ a 44 ∈ [0,2] ∧ a 20 ∈ [0] ∧ a 21 ∈ [0,1] ∧ a 47 ∈ [0,2,3] := by
  have b0 : a 12 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 12) (a 8) 1 d8 c33 (by decide +kernel)
  have t0 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b0
  have b1 : a 25 ≠ 1 := exclude [0,1] (fun u v => edge r37 v u) (a 25) (a 9) 1 d9 c37 (by decide +kernel)
  have t1 : a 25 ∈ [0,2,3] := remove (a 25) 1 [0,1,2,3] d25 b1
  have b2 : a 25 ≠ 3 := exclude [0,1] (fun u v => edge r37 v u) (a 25) (a 9) 3 d9 c37 (by decide +kernel)
  have t2 : a 25 ∈ [0,2] := remove (a 25) 3 [0,2,3] t1 b2
  have b3 : a 39 ≠ 2 := exclude [0,1] (fun u v => edge r38 v u) (a 39) (a 9) 2 d9 c38 (by decide +kernel)
  have t3 : a 39 ∈ [0,1,3] := remove (a 39) 2 [0,1,2,3] d39 b3
  have b4 : a 39 ≠ 3 := exclude [0,1] (fun u v => edge r38 v u) (a 39) (a 9) 3 d9 c38 (by decide +kernel)
  have t4 : a 39 ∈ [0,1] := remove (a 39) 3 [0,1,3] t3 b4
  have b5 : a 42 ≠ 2 := exclude [0] (fun u v => edge r48 v u) (a 42) (a 12) 2 t0 c48 (by decide +kernel)
  have t5 : a 42 ∈ [0,1,3] := remove (a 42) 2 [0,1,2,3] d42 b5
  have b6 : a 42 ≠ 3 := exclude [0] (fun u v => edge r48 v u) (a 42) (a 12) 3 t0 c48 (by decide +kernel)
  have t6 : a 42 ∈ [0,1] := remove (a 42) 3 [0,1,3] t5 b6
  have b7 : a 16 ≠ 1 := exclude [0,1] (fun u v => edge r51 v u) (a 16) (a 14) 1 d14 c51 (by decide +kernel)
  have t7 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b7
  have b8 : a 18 ≠ 1 := exclude [0,1] (fun u v => edge r52 v u) (a 18) (a 14) 1 d14 c52 (by decide +kernel)
  have t8 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b8
  have b9 : a 18 ≠ 3 := exclude [0,1] (fun u v => edge r52 v u) (a 18) (a 14) 3 d14 c52 (by decide +kernel)
  have t9 : a 18 ∈ [0,2] := remove (a 18) 3 [0,2,3] t8 b9
  have b10 : a 44 ≠ 1 := exclude [0,1] (fun u v => edge r54 v u) (a 44) (a 14) 1 d14 c54 (by decide +kernel)
  have t10 : a 44 ∈ [0,2,3] := remove (a 44) 1 [0,1,2,3] d44 b10
  have b11 : a 44 ≠ 3 := exclude [0,1] (fun u v => edge r54 v u) (a 44) (a 14) 3 d14 c54 (by decide +kernel)
  have t11 : a 44 ∈ [0,2] := remove (a 44) 3 [0,2,3] t10 b11
  have b12 : a 20 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 20) (a 16) 1 t7 c60 (by decide +kernel)
  have t12 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b12
  have b13 : a 21 ≠ 2 := exclude [0,1] (fun u v => edge r63 v u) (a 21) (a 17) 2 d17 c63 (by decide +kernel)
  have t13 : a 21 ∈ [0,1,3] := remove (a 21) 2 [0,1,2,3] d21 b13
  have b14 : a 21 ≠ 3 := exclude [0,1] (fun u v => edge r63 v u) (a 21) (a 17) 3 d17 c63 (by decide +kernel)
  have t14 : a 21 ∈ [0,1] := remove (a 21) 3 [0,1,3] t13 b14
  have b15 : a 47 ≠ 1 := exclude [0,1] (fun u v => edge r65 v u) (a 47) (a 17) 1 d17 c65 (by decide +kernel)
  have t15 : a 47 ∈ [0,2,3] := remove (a 47) 1 [0,1,2,3] d47 b15
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t14 (t15)))))))))

theorem chunk2 (a : Nat → Nat)
    (d47 : a 47 ∈ [0,2,3])
    (d17 : a 17 ∈ [0,1])
    (d48 : a 48 ∈ [0,1,2,3])
    (d18 : a 18 ∈ [0,2])
    (d51 : a 51 ∈ [0,1])
    (d21 : a 21 ∈ [0,1])
    (d23 : a 23 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d52 : a 52 ∈ [0,1,2,3])
    (d27 : a 27 ∈ [0,1])
    (d55 : a 55 ∈ [0,1,2,3])
    (d25 : a 25 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3])
    (d29 : a 29 ∈ [0,2])
    (d33 : a 33 ∈ [0,1])
    (d35 : a 35 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0])
    (d37 : a 37 ∈ [0,1])
    (d36 : a 36 ∈ [0,2])
    (c65 : edge r65 (a 17) (a 47)=true)
    (c69 : edge r69 (a 18) (a 48)=true)
    (c76 : edge r76 (a 21) (a 51)=true)
    (c77 : edge r77 (a 22) (a 23)=true)
    (c80 : edge r80 (a 22) (a 52)=true)
    (c82 : edge r82 (a 23) (a 27)=true)
    (c87 : edge r87 (a 25) (a 55)=true)
    (c93 : edge r93 (a 29) (a 31)=true)
    (c94 : edge r94 (a 29) (a 33)=true)
    (c104 : edge r104 (a 32) (a 35)=true)
    (c115 : edge r115 (a 36) (a 37)=true)
    : a 47 ∈ [0,2] ∧ a 48 ∈ [0,1] ∧ a 51 ∈ [0] ∧ a 23 ∈ [0] ∧ a 52 ∈ [0,1] ∧ a 27 ∈ [0] ∧ a 55 ∈ [0,2] ∧ a 31 ∈ [0,1] ∧ a 33 ∈ [0] ∧ a 35 ∈ [0,2] ∧ a 37 ∈ [0] := by
  have b0 : a 47 ≠ 3 := exclude [0,1] (fun u v => edge r65 v u) (a 47) (a 17) 3 d17 c65 (by decide +kernel)
  have t0 : a 47 ∈ [0,2] := remove (a 47) 3 [0,2,3] d47 b0
  have b1 : a 48 ≠ 2 := exclude [0,2] (fun u v => edge r69 v u) (a 48) (a 18) 2 d18 c69 (by decide +kernel)
  have t1 : a 48 ∈ [0,1,3] := remove (a 48) 2 [0,1,2,3] d48 b1
  have b2 : a 48 ≠ 3 := exclude [0,2] (fun u v => edge r69 v u) (a 48) (a 18) 3 d18 c69 (by decide +kernel)
  have t2 : a 48 ∈ [0,1] := remove (a 48) 3 [0,1,3] t1 b2
  have b3 : a 51 ≠ 1 := exclude [0,1] (fun u v => edge r76 v u) (a 51) (a 21) 1 d21 c76 (by decide +kernel)
  have t3 : a 51 ∈ [0] := remove (a 51) 1 [0,1] d51 b3
  have b4 : a 23 ≠ 1 := exclude [0,2] (fun u v => edge r77 v u) (a 23) (a 22) 1 d22 c77 (by decide +kernel)
  have t4 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b4
  have b5 : a 52 ≠ 2 := exclude [0,2] (fun u v => edge r80 v u) (a 52) (a 22) 2 d22 c80 (by decide +kernel)
  have t5 : a 52 ∈ [0,1,3] := remove (a 52) 2 [0,1,2,3] d52 b5
  have b6 : a 52 ≠ 3 := exclude [0,2] (fun u v => edge r80 v u) (a 52) (a 22) 3 d22 c80 (by decide +kernel)
  have t6 : a 52 ∈ [0,1] := remove (a 52) 3 [0,1,3] t5 b6
  have b7 : a 27 ≠ 1 := exclude [0] (fun u v => edge r82 v u) (a 27) (a 23) 1 t4 c82 (by decide +kernel)
  have t7 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b7
  have b8 : a 55 ≠ 1 := exclude [0,2] (fun u v => edge r87 v u) (a 55) (a 25) 1 d25 c87 (by decide +kernel)
  have t8 : a 55 ∈ [0,2,3] := remove (a 55) 1 [0,1,2,3] d55 b8
  have b9 : a 55 ≠ 3 := exclude [0,2] (fun u v => edge r87 v u) (a 55) (a 25) 3 d25 c87 (by decide +kernel)
  have t9 : a 55 ∈ [0,2] := remove (a 55) 3 [0,2,3] t8 b9
  have b10 : a 31 ≠ 2 := exclude [0,2] (fun u v => edge r93 v u) (a 31) (a 29) 2 d29 c93 (by decide +kernel)
  have t10 : a 31 ∈ [0,1,3] := remove (a 31) 2 [0,1,2,3] d31 b10
  have b11 : a 31 ≠ 3 := exclude [0,2] (fun u v => edge r93 v u) (a 31) (a 29) 3 d29 c93 (by decide +kernel)
  have t11 : a 31 ∈ [0,1] := remove (a 31) 3 [0,1,3] t10 b11
  have b12 : a 33 ≠ 1 := exclude [0,2] (fun u v => edge r94 v u) (a 33) (a 29) 1 d29 c94 (by decide +kernel)
  have t12 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b12
  have b13 : a 35 ≠ 1 := exclude [0] (fun u v => edge r104 v u) (a 35) (a 32) 1 d32 c104 (by decide +kernel)
  have t13 : a 35 ∈ [0,2,3] := remove (a 35) 1 [0,1,2,3] d35 b13
  have b14 : a 35 ≠ 3 := exclude [0] (fun u v => edge r104 v u) (a 35) (a 32) 3 d32 c104 (by decide +kernel)
  have t14 : a 35 ∈ [0,2] := remove (a 35) 3 [0,2,3] t13 b14
  have b15 : a 37 ≠ 1 := exclude [0,2] (fun u v => edge r115 v u) (a 37) (a 36) 1 d36 c115 (by decide +kernel)
  have t15 : a 37 ∈ [0] := remove (a 37) 1 [0,1] d37 b15
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t9 (And.intro t11 (And.intro t12 (And.intro t14 (t15))))))))))

theorem chunk3 (a : Nat → Nat)
    (d41 : a 41 ∈ [0,1])
    (d37 : a 37 ∈ [0])
    (d57 : a 57 ∈ [0,1,2,3])
    (d42 : a 42 ∈ [0,1])
    (d45 : a 45 ∈ [0,1])
    (d44 : a 44 ∈ [0,2])
    (d49 : a 49 ∈ [0,1,2,3])
    (d58 : a 58 ∈ [0,1,2,3])
    (d51 : a 51 ∈ [0])
    (d54 : a 54 ∈ [0,1])
    (d52 : a 52 ∈ [0,1])
    (d6 : a 6 ∈ [0,1,2,3])
    (d12 : a 12 ∈ [0])
    (d11 : a 11 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (c26 : edge r26 (a 6) (a 12)=true)
    (c44 : edge r44 (a 11) (a 27)=true)
    (c120 : edge r120 (a 37) (a 41)=true)
    (c132 : edge r132 (a 42) (a 57)=true)
    (c134 : edge r134 (a 44) (a 45)=true)
    (c139 : edge r139 (a 45) (a 49)=true)
    (c152 : edge r152 (a 51) (a 58)=true)
    (c154 : edge r154 (a 52) (a 54)=true)
    : a 41 ∈ [0] ∧ a 57 ∈ [0,2] ∧ a 45 ∈ [0] ∧ a 49 ∈ [0,1] ∧ a 58 ∈ [0,2] ∧ a 54 ∈ [0] ∧ a 6 ∈ [0,2] ∧ a 11 ∈ [0] := by
  have b0 : a 41 ≠ 1 := exclude [0] (fun u v => edge r120 v u) (a 41) (a 37) 1 d37 c120 (by decide +kernel)
  have t0 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b0
  have b1 : a 57 ≠ 1 := exclude [0,1] (fun u v => edge r132 v u) (a 57) (a 42) 1 d42 c132 (by decide +kernel)
  have t1 : a 57 ∈ [0,2,3] := remove (a 57) 1 [0,1,2,3] d57 b1
  have b2 : a 57 ≠ 3 := exclude [0,1] (fun u v => edge r132 v u) (a 57) (a 42) 3 d42 c132 (by decide +kernel)
  have t2 : a 57 ∈ [0,2] := remove (a 57) 3 [0,2,3] t1 b2
  have b3 : a 45 ≠ 1 := exclude [0,2] (fun u v => edge r134 v u) (a 45) (a 44) 1 d44 c134 (by decide +kernel)
  have t3 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b3
  have b4 : a 49 ≠ 2 := exclude [0] (fun u v => edge r139 v u) (a 49) (a 45) 2 t3 c139 (by decide +kernel)
  have t4 : a 49 ∈ [0,1,3] := remove (a 49) 2 [0,1,2,3] d49 b4
  have b5 : a 49 ≠ 3 := exclude [0] (fun u v => edge r139 v u) (a 49) (a 45) 3 t3 c139 (by decide +kernel)
  have t5 : a 49 ∈ [0,1] := remove (a 49) 3 [0,1,3] t4 b5
  have b6 : a 58 ≠ 1 := exclude [0] (fun u v => edge r152 v u) (a 58) (a 51) 1 d51 c152 (by decide +kernel)
  have t6 : a 58 ∈ [0,2,3] := remove (a 58) 1 [0,1,2,3] d58 b6
  have b7 : a 58 ≠ 3 := exclude [0] (fun u v => edge r152 v u) (a 58) (a 51) 3 d51 c152 (by decide +kernel)
  have t7 : a 58 ∈ [0,2] := remove (a 58) 3 [0,2,3] t6 b7
  have b8 : a 54 ≠ 1 := exclude [0,1] (fun u v => edge r154 v u) (a 54) (a 52) 1 d52 c154 (by decide +kernel)
  have t8 : a 54 ∈ [0] := remove (a 54) 1 [0,1] d54 b8
  have b9 : a 6 ≠ 1 := exclude [0] (edge r26) (a 6) (a 12) 1 d12 c26 (by decide +kernel)
  have t9 : a 6 ∈ [0,2,3] := remove (a 6) 1 [0,1,2,3] d6 b9
  have b10 : a 6 ≠ 3 := exclude [0] (edge r26) (a 6) (a 12) 3 d12 c26 (by decide +kernel)
  have t10 : a 6 ∈ [0,2] := remove (a 6) 3 [0,2,3] t9 b10
  have b11 : a 11 ≠ 1 := exclude [0] (edge r44) (a 11) (a 27) 1 d27 c44 (by decide +kernel)
  have t11 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b11
  exact And.intro t0 (And.intro t2 (And.intro t3 (And.intro t5 (And.intro t7 (And.intro t8 (And.intro t10 (t11)))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_238
