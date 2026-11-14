import PartitionData205_244
namespace PartitionCover205_244
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk0 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d0 : a 0 ∈ [0])
    (d4 : a 4 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d16 : a 16 ∈ [0,1,2,3])
    (d32 : a 32 ∈ [0,1,2,3])
    (d5 : a 5 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d9 : a 9 ∈ [0,1])
    (d17 : a 17 ∈ [0,1])
    (d33 : a 33 ∈ [0,1])
    (d6 : a 6 ∈ [0,1])
    (d10 : a 10 ∈ [0,1,2,3])
    (c1 : edge r1 (a 0) (a 2)=true)
    (c2 : edge r2 (a 0) (a 4)=true)
    (c3 : edge r3 (a 0) (a 8)=true)
    (c4 : edge r4 (a 0) (a 16)=true)
    (c5 : edge r5 (a 0) (a 32)=true)
    (c7 : edge r7 (a 1) (a 5)=true)
    (c8 : edge r8 (a 1) (a 9)=true)
    (c9 : edge r9 (a 1) (a 17)=true)
    (c10 : edge r10 (a 1) (a 33)=true)
    (c12 : edge r12 (a 2) (a 6)=true)
    (c13 : edge r13 (a 2) (a 10)=true)
    : a 2 ∈ [0] ∧ a 4 ∈ [0] ∧ a 8 ∈ [0] ∧ a 16 ∈ [0] ∧ a 32 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 33 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0,3] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r1 v u) (a 2) (a 0) 1 d0 c1 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 4 ≠ 1 := exclude [0] (fun u v => edge r2 v u) (a 4) (a 0) 1 d0 c2 (by decide +kernel)
  have t1 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b1
  have b2 : a 8 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 8) (a 0) 1 d0 c3 (by decide +kernel)
  have t2 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b2
  have b3 : a 16 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 1 d0 c4 (by decide +kernel)
  have t3 : a 16 ∈ [0,2,3] := remove (a 16) 1 [0,1,2,3] d16 b3
  have b4 : a 16 ≠ 2 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 2 d0 c4 (by decide +kernel)
  have t4 : a 16 ∈ [0,3] := remove (a 16) 2 [0,2,3] t3 b4
  have b5 : a 16 ≠ 3 := exclude [0] (fun u v => edge r4 v u) (a 16) (a 0) 3 d0 c4 (by decide +kernel)
  have t5 : a 16 ∈ [0] := remove (a 16) 3 [0,3] t4 b5
  have b6 : a 32 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 32) (a 0) 1 d0 c5 (by decide +kernel)
  have t6 : a 32 ∈ [0,2,3] := remove (a 32) 1 [0,1,2,3] d32 b6
  have b7 : a 32 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 32) (a 0) 2 d0 c5 (by decide +kernel)
  have t7 : a 32 ∈ [0,3] := remove (a 32) 2 [0,2,3] t6 b7
  have b8 : a 32 ≠ 3 := exclude [0] (fun u v => edge r5 v u) (a 32) (a 0) 3 d0 c5 (by decide +kernel)
  have t8 : a 32 ∈ [0] := remove (a 32) 3 [0,3] t7 b8
  have b9 : a 5 ≠ 1 := exclude [0] (fun u v => edge r7 v u) (a 5) (a 1) 1 d1 c7 (by decide +kernel)
  have t9 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b9
  have b10 : a 9 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 9) (a 1) 1 d1 c8 (by decide +kernel)
  have t10 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b10
  have b11 : a 17 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 17) (a 1) 1 d1 c9 (by decide +kernel)
  have t11 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b11
  have b12 : a 33 ≠ 1 := exclude [0] (fun u v => edge r10 v u) (a 33) (a 1) 1 d1 c10 (by decide +kernel)
  have t12 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b12
  have b13 : a 6 ≠ 1 := exclude [0] (fun u v => edge r12 v u) (a 6) (a 2) 1 t0 c12 (by decide +kernel)
  have t13 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b13
  have b14 : a 10 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 1 t0 c13 (by decide +kernel)
  have t14 : a 10 ∈ [0,2,3] := remove (a 10) 1 [0,1,2,3] d10 b14
  have b15 : a 10 ≠ 2 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 2 t0 c13 (by decide +kernel)
  have t15 : a 10 ∈ [0,3] := remove (a 10) 2 [0,2,3] t14 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t5 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (t15))))))))))

theorem chunk1 (a : Nat → Nat)
    (d10 : a 10 ∈ [0,3])
    (d2 : a 2 ∈ [0])
    (d18 : a 18 ∈ [0,1,2,3])
    (d34 : a 34 ∈ [0,1,2,3])
    (d35 : a 35 ∈ [0,1])
    (d3 : a 3 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d4 : a 4 ∈ [0])
    (d36 : a 36 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d5 : a 5 ∈ [0])
    (d21 : a 21 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d6 : a 6 ∈ [0])
    (d38 : a 38 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d23 : a 23 ∈ [0,1,2,3])
    (c13 : edge r13 (a 2) (a 10)=true)
    (c14 : edge r14 (a 2) (a 18)=true)
    (c15 : edge r15 (a 2) (a 34)=true)
    (c19 : edge r19 (a 3) (a 35)=true)
    (c23 : edge r23 (a 4) (a 20)=true)
    (c24 : edge r24 (a 4) (a 36)=true)
    (c26 : edge r26 (a 5) (a 13)=true)
    (c27 : edge r27 (a 5) (a 21)=true)
    (c29 : edge r29 (a 6) (a 7)=true)
    (c32 : edge r32 (a 6) (a 38)=true)
    (c33 : edge r33 (a 7) (a 15)=true)
    (c34 : edge r34 (a 7) (a 23)=true)
    : a 10 ∈ [0] ∧ a 18 ∈ [0] ∧ a 34 ∈ [0] ∧ a 35 ∈ [0] ∧ a 20 ∈ [0] ∧ a 36 ∈ [0] ∧ a 13 ∈ [0] ∧ a 21 ∈ [0] ∧ a 7 ∈ [0] ∧ a 38 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0,1,3] := by
  have b0 : a 10 ≠ 3 := exclude [0] (fun u v => edge r13 v u) (a 10) (a 2) 3 d2 c13 (by decide +kernel)
  have t0 : a 10 ∈ [0] := remove (a 10) 3 [0,3] d10 b0
  have b1 : a 18 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 18) (a 2) 1 d2 c14 (by decide +kernel)
  have t1 : a 18 ∈ [0,2,3] := remove (a 18) 1 [0,1,2,3] d18 b1
  have b2 : a 18 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 18) (a 2) 2 d2 c14 (by decide +kernel)
  have t2 : a 18 ∈ [0,3] := remove (a 18) 2 [0,2,3] t1 b2
  have b3 : a 18 ≠ 3 := exclude [0] (fun u v => edge r14 v u) (a 18) (a 2) 3 d2 c14 (by decide +kernel)
  have t3 : a 18 ∈ [0] := remove (a 18) 3 [0,3] t2 b3
  have b4 : a 34 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 34) (a 2) 1 d2 c15 (by decide +kernel)
  have t4 : a 34 ∈ [0,2,3] := remove (a 34) 1 [0,1,2,3] d34 b4
  have b5 : a 34 ≠ 2 := exclude [0] (fun u v => edge r15 v u) (a 34) (a 2) 2 d2 c15 (by decide +kernel)
  have t5 : a 34 ∈ [0,3] := remove (a 34) 2 [0,2,3] t4 b5
  have b6 : a 34 ≠ 3 := exclude [0] (fun u v => edge r15 v u) (a 34) (a 2) 3 d2 c15 (by decide +kernel)
  have t6 : a 34 ∈ [0] := remove (a 34) 3 [0,3] t5 b6
  have b7 : a 35 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 35) (a 3) 1 d3 c19 (by decide +kernel)
  have t7 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b7
  have b8 : a 20 ≠ 1 := exclude [0] (fun u v => edge r23 v u) (a 20) (a 4) 1 d4 c23 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b8
  have b9 : a 36 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 36) (a 4) 1 d4 c24 (by decide +kernel)
  have t9 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b9
  have b10 : a 13 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 13) (a 5) 1 d5 c26 (by decide +kernel)
  have t10 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b10
  have b11 : a 21 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 21) (a 5) 1 d5 c27 (by decide +kernel)
  have t11 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b11
  have b12 : a 7 ≠ 1 := exclude [0] (fun u v => edge r29 v u) (a 7) (a 6) 1 d6 c29 (by decide +kernel)
  have t12 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b12
  have b13 : a 38 ≠ 1 := exclude [0] (fun u v => edge r32 v u) (a 38) (a 6) 1 d6 c32 (by decide +kernel)
  have t13 : a 38 ∈ [0] := remove (a 38) 1 [0,1] d38 b13
  have b14 : a 15 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 15) (a 7) 1 t12 c33 (by decide +kernel)
  have t14 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b14
  have b15 : a 23 ≠ 2 := exclude [0] (fun u v => edge r34 v u) (a 23) (a 7) 2 t12 c34 (by decide +kernel)
  have t15 : a 23 ∈ [0,1,3] := remove (a 23) 2 [0,1,2,3] d23 b15
  exact And.intro t0 (And.intro t3 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))

theorem chunk2 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,1,3])
    (d7 : a 7 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d8 : a 8 ∈ [0])
    (d24 : a 24 ∈ [0,1,2,3])
    (d40 : a 40 ∈ [0,1,2,3])
    (d11 : a 11 ∈ [0,1])
    (d9 : a 9 ∈ [0])
    (d14 : a 14 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d26 : a 26 ∈ [0,1,2,3])
    (d42 : a 42 ∈ [0,1,2,3])
    (d28 : a 28 ∈ [0,1])
    (c34 : edge r34 (a 7) (a 23)=true)
    (c35 : edge r35 (a 7) (a 39)=true)
    (c38 : edge r38 (a 8) (a 12)=true)
    (c39 : edge r39 (a 8) (a 24)=true)
    (c40 : edge r40 (a 8) (a 40)=true)
    (c41 : edge r41 (a 9) (a 11)=true)
    (c46 : edge r46 (a 10) (a 14)=true)
    (c47 : edge r47 (a 10) (a 26)=true)
    (c48 : edge r48 (a 10) (a 42)=true)
    (c54 : edge r54 (a 12) (a 28)=true)
    : a 23 ∈ [0,1] ∧ a 39 ∈ [0] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0,1] ∧ a 40 ∈ [0,1] ∧ a 11 ∈ [0] ∧ a 14 ∈ [0] ∧ a 26 ∈ [0] ∧ a 42 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 23 ≠ 3 := exclude [0] (fun u v => edge r34 v u) (a 23) (a 7) 3 d7 c34 (by decide +kernel)
  have t0 : a 23 ∈ [0,1] := remove (a 23) 3 [0,1,3] d23 b0
  have b1 : a 39 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 39) (a 7) 1 d7 c35 (by decide +kernel)
  have t1 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b1
  have b2 : a 12 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 12) (a 8) 1 d8 c38 (by decide +kernel)
  have t2 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b2
  have b3 : a 24 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 24) (a 8) 2 d8 c39 (by decide +kernel)
  have t3 : a 24 ∈ [0,1,3] := remove (a 24) 2 [0,1,2,3] d24 b3
  have b4 : a 24 ≠ 3 := exclude [0] (fun u v => edge r39 v u) (a 24) (a 8) 3 d8 c39 (by decide +kernel)
  have t4 : a 24 ∈ [0,1] := remove (a 24) 3 [0,1,3] t3 b4
  have b5 : a 40 ≠ 2 := exclude [0] (fun u v => edge r40 v u) (a 40) (a 8) 2 d8 c40 (by decide +kernel)
  have t5 : a 40 ∈ [0,1,3] := remove (a 40) 2 [0,1,2,3] d40 b5
  have b6 : a 40 ≠ 3 := exclude [0] (fun u v => edge r40 v u) (a 40) (a 8) 3 d8 c40 (by decide +kernel)
  have t6 : a 40 ∈ [0,1] := remove (a 40) 3 [0,1,3] t5 b6
  have b7 : a 11 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 11) (a 9) 1 d9 c41 (by decide +kernel)
  have t7 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b7
  have b8 : a 14 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 14) (a 10) 1 d10 c46 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b8
  have b9 : a 26 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 26) (a 10) 1 d10 c47 (by decide +kernel)
  have t9 : a 26 ∈ [0,2,3] := remove (a 26) 1 [0,1,2,3] d26 b9
  have b10 : a 26 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 26) (a 10) 2 d10 c47 (by decide +kernel)
  have t10 : a 26 ∈ [0,3] := remove (a 26) 2 [0,2,3] t9 b10
  have b11 : a 26 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 26) (a 10) 3 d10 c47 (by decide +kernel)
  have t11 : a 26 ∈ [0] := remove (a 26) 3 [0,3] t10 b11
  have b12 : a 42 ≠ 1 := exclude [0] (fun u v => edge r48 v u) (a 42) (a 10) 1 d10 c48 (by decide +kernel)
  have t12 : a 42 ∈ [0,2,3] := remove (a 42) 1 [0,1,2,3] d42 b12
  have b13 : a 42 ≠ 2 := exclude [0] (fun u v => edge r48 v u) (a 42) (a 10) 2 d10 c48 (by decide +kernel)
  have t13 : a 42 ∈ [0,3] := remove (a 42) 2 [0,2,3] t12 b13
  have b14 : a 42 ≠ 3 := exclude [0] (fun u v => edge r48 v u) (a 42) (a 10) 3 d10 c48 (by decide +kernel)
  have t14 : a 42 ∈ [0] := remove (a 42) 3 [0,3] t13 b14
  have b15 : a 28 ≠ 1 := exclude [0] (fun u v => edge r54 v u) (a 28) (a 12) 1 t2 c54 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t4 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t11 (And.intro t14 (t15)))))))))

theorem chunk3 (a : Nat → Nat)
    (d44 : a 44 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d29 : a 29 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d45 : a 45 ∈ [0,1])
    (d46 : a 46 ∈ [0,1,2,3])
    (d14 : a 14 ∈ [0])
    (d47 : a 47 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d24 : a 24 ∈ [0,1])
    (d16 : a 16 ∈ [0])
    (d48 : a 48 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d22 : a 22 ∈ [0,1])
    (d18 : a 18 ∈ [0])
    (d50 : a 50 ∈ [0,1,2,3])
    (d23 : a 23 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (c55 : edge r55 (a 12) (a 44)=true)
    (c57 : edge r57 (a 13) (a 29)=true)
    (c58 : edge r58 (a 13) (a 45)=true)
    (c61 : edge r61 (a 14) (a 46)=true)
    (c63 : edge r63 (a 15) (a 47)=true)
    (c67 : edge r67 (a 16) (a 24)=true)
    (c68 : edge r68 (a 16) (a 48)=true)
    (c69 : edge r69 (a 17) (a 19)=true)
    (c74 : edge r74 (a 18) (a 22)=true)
    (c76 : edge r76 (a 18) (a 50)=true)
    (c84 : edge r84 (a 21) (a 23)=true)
    : a 44 ∈ [0] ∧ a 29 ∈ [0] ∧ a 45 ∈ [0] ∧ a 46 ∈ [0,1] ∧ a 47 ∈ [0] ∧ a 24 ∈ [0] ∧ a 48 ∈ [0] ∧ a 19 ∈ [0] ∧ a 22 ∈ [0] ∧ a 50 ∈ [0] ∧ a 23 ∈ [0] := by
  have b0 : a 44 ≠ 1 := exclude [0] (fun u v => edge r55 v u) (a 44) (a 12) 1 d12 c55 (by decide +kernel)
  have t0 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b0
  have b1 : a 29 ≠ 1 := exclude [0] (fun u v => edge r57 v u) (a 29) (a 13) 1 d13 c57 (by decide +kernel)
  have t1 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b1
  have b2 : a 45 ≠ 1 := exclude [0] (fun u v => edge r58 v u) (a 45) (a 13) 1 d13 c58 (by decide +kernel)
  have t2 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b2
  have b3 : a 46 ≠ 2 := exclude [0] (fun u v => edge r61 v u) (a 46) (a 14) 2 d14 c61 (by decide +kernel)
  have t3 : a 46 ∈ [0,1,3] := remove (a 46) 2 [0,1,2,3] d46 b3
  have b4 : a 46 ≠ 3 := exclude [0] (fun u v => edge r61 v u) (a 46) (a 14) 3 d14 c61 (by decide +kernel)
  have t4 : a 46 ∈ [0,1] := remove (a 46) 3 [0,1,3] t3 b4
  have b5 : a 47 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 47) (a 15) 1 d15 c63 (by decide +kernel)
  have t5 : a 47 ∈ [0] := remove (a 47) 1 [0,1] d47 b5
  have b6 : a 24 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 24) (a 16) 1 d16 c67 (by decide +kernel)
  have t6 : a 24 ∈ [0] := remove (a 24) 1 [0,1] d24 b6
  have b7 : a 48 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 48) (a 16) 1 d16 c68 (by decide +kernel)
  have t7 : a 48 ∈ [0,2,3] := remove (a 48) 1 [0,1,2,3] d48 b7
  have b8 : a 48 ≠ 2 := exclude [0] (fun u v => edge r68 v u) (a 48) (a 16) 2 d16 c68 (by decide +kernel)
  have t8 : a 48 ∈ [0,3] := remove (a 48) 2 [0,2,3] t7 b8
  have b9 : a 48 ≠ 3 := exclude [0] (fun u v => edge r68 v u) (a 48) (a 16) 3 d16 c68 (by decide +kernel)
  have t9 : a 48 ∈ [0] := remove (a 48) 3 [0,3] t8 b9
  have b10 : a 19 ≠ 1 := exclude [0] (fun u v => edge r69 v u) (a 19) (a 17) 1 d17 c69 (by decide +kernel)
  have t10 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b10
  have b11 : a 22 ≠ 1 := exclude [0] (fun u v => edge r74 v u) (a 22) (a 18) 1 d18 c74 (by decide +kernel)
  have t11 : a 22 ∈ [0] := remove (a 22) 1 [0,1] d22 b11
  have b12 : a 50 ≠ 1 := exclude [0] (fun u v => edge r76 v u) (a 50) (a 18) 1 d18 c76 (by decide +kernel)
  have t12 : a 50 ∈ [0,2,3] := remove (a 50) 1 [0,1,2,3] d50 b12
  have b13 : a 50 ≠ 2 := exclude [0] (fun u v => edge r76 v u) (a 50) (a 18) 2 d18 c76 (by decide +kernel)
  have t13 : a 50 ∈ [0,3] := remove (a 50) 2 [0,2,3] t12 b13
  have b14 : a 50 ≠ 3 := exclude [0] (fun u v => edge r76 v u) (a 50) (a 18) 3 d18 c76 (by decide +kernel)
  have t14 : a 50 ∈ [0] := remove (a 50) 3 [0,3] t13 b14
  have b15 : a 23 ≠ 1 := exclude [0] (fun u v => edge r84 v u) (a 23) (a 21) 1 d21 c84 (by decide +kernel)
  have t15 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t14 (t15))))))))))

#print axioms chunk0
#print axioms chunk1
#print axioms chunk2
#print axioms chunk3
end PartitionCover205_244
