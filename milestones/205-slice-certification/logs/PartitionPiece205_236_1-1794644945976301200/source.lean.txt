import PartitionData205_236
namespace PartitionCover205_236
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d6 : a 6 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d3 : a 3 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d17 : a 17 ∈ [0,1])
    (d10 : a 10 ∈ [0,2])
    (d20 : a 20 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d23 : a 23 ∈ [0,2])
    (d33 : a 33 ∈ [0,1])
    (c3 : edge r3 (a 1) (a 2)=true)
    (c4 : edge r4 (a 1) (a 6)=true)
    (c5 : edge r5 (a 2) (a 4)=true)
    (c7 : edge r7 (a 2) (a 14)=true)
    (c8 : edge r8 (a 2) (a 27)=true)
    (c9 : edge r9 (a 3) (a 4)=true)
    (c10 : edge r10 (a 3) (a 11)=true)
    (c11 : edge r11 (a 3) (a 17)=true)
    (c19 : edge r19 (a 6) (a 10)=true)
    (c20 : edge r20 (a 6) (a 20)=true)
    (c21 : edge r21 (a 6) (a 31)=true)
    (c23 : edge r23 (a 7) (a 11)=true)
    (c24 : edge r24 (a 7) (a 21)=true)
    (c27 : edge r27 (a 9) (a 10)=true)
    (c29 : edge r29 (a 9) (a 23)=true)
    (c30 : edge r30 (a 9) (a 33)=true)
    : a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 4 ∈ [0] ∧ a 14 ∈ [0] ∧ a 27 ∈ [0] ∧ a 3 ∈ [0] ∧ a 11 ∈ [0] ∧ a 17 ∈ [0] ∧ a 10 ∈ [0] ∧ a 20 ∈ [0] ∧ a 31 ∈ [0] ∧ a 7 ∈ [0] ∧ a 21 ∈ [0] ∧ a 9 ∈ [0] ∧ a 23 ∈ [0] ∧ a 33 ∈ [0] := by
  have b0 : a 2 ≠ 1 := exclude [0] (fun u v => edge r3 v u) (a 2) (a 1) 1 d1 c3 (by decide +kernel)
  have t0 : a 2 ∈ [0] := remove (a 2) 1 [0,1] d2 b0
  have b1 : a 6 ≠ 1 := exclude [0] (fun u v => edge r4 v u) (a 6) (a 1) 1 d1 c4 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 1 [0,1] d6 b1
  have b2 : a 4 ≠ 2 := exclude [0] (fun u v => edge r5 v u) (a 4) (a 2) 2 t0 c5 (by decide +kernel)
  have t2 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b2
  have b3 : a 14 ≠ 2 := exclude [0] (fun u v => edge r7 v u) (a 14) (a 2) 2 t0 c7 (by decide +kernel)
  have t3 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b3
  have b4 : a 27 ≠ 1 := exclude [0] (fun u v => edge r8 v u) (a 27) (a 2) 1 t0 c8 (by decide +kernel)
  have t4 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b4
  have b5 : a 3 ≠ 2 := exclude [0] (edge r9) (a 3) (a 4) 2 t2 c9 (by decide +kernel)
  have t5 : a 3 ∈ [0] := remove (a 3) 2 [0,2] d3 b5
  have b6 : a 11 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 11) (a 3) 2 t5 c10 (by decide +kernel)
  have t6 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b6
  have b7 : a 17 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 17) (a 3) 1 t5 c11 (by decide +kernel)
  have t7 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b7
  have b8 : a 10 ≠ 2 := exclude [0] (fun u v => edge r19 v u) (a 10) (a 6) 2 t1 c19 (by decide +kernel)
  have t8 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b8
  have b9 : a 20 ≠ 2 := exclude [0] (fun u v => edge r20 v u) (a 20) (a 6) 2 t1 c20 (by decide +kernel)
  have t9 : a 20 ∈ [0] := remove (a 20) 2 [0,2] d20 b9
  have b10 : a 31 ≠ 1 := exclude [0] (fun u v => edge r21 v u) (a 31) (a 6) 1 t1 c21 (by decide +kernel)
  have t10 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b10
  have b11 : a 7 ≠ 2 := exclude [0] (edge r23) (a 7) (a 11) 2 t6 c23 (by decide +kernel)
  have t11 : a 7 ∈ [0] := remove (a 7) 2 [0,2] d7 b11
  have b12 : a 21 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 21) (a 7) 1 t11 c24 (by decide +kernel)
  have t12 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b12
  have b13 : a 9 ≠ 2 := exclude [0] (edge r27) (a 9) (a 10) 2 t8 c27 (by decide +kernel)
  have t13 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b13
  have b14 : a 23 ≠ 2 := exclude [0] (fun u v => edge r29 v u) (a 23) (a 9) 2 t13 c29 (by decide +kernel)
  have t14 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b14
  have b15 : a 33 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 33) (a 9) 1 t13 c30 (by decide +kernel)
  have t15 : a 33 ∈ [0] := remove (a 33) 1 [0,1] d33 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk5 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2])
    (d11 : a 11 ∈ [0])
    (d35 : a 35 ∈ [0,1])
    (d13 : a 13 ∈ [0,2])
    (d14 : a 14 ∈ [0])
    (d39 : a 39 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (d15 : a 15 ∈ [0,1])
    (d17 : a 17 ∈ [0])
    (d40 : a 40 ∈ [0,1])
    (d41 : a 41 ∈ [0,1])
    (d19 : a 19 ∈ [0,2])
    (d20 : a 20 ∈ [0])
    (d43 : a 43 ∈ [0,2])
    (d44 : a 44 ∈ [0,1])
    (d21 : a 21 ∈ [0])
    (d25 : a 25 ∈ [0,2])
    (d45 : a 45 ∈ [0,1])
    (d48 : a 48 ∈ [0,1])
    (d49 : a 49 ∈ [0,1])
    (d26 : a 26 ∈ [0,1])
    (d27 : a 27 ∈ [0])
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
    : a 24 ∈ [0] ∧ a 35 ∈ [0] ∧ a 13 ∈ [0] ∧ a 39 ∈ [0] ∧ a 22 ∈ [0] ∧ a 15 ∈ [0] ∧ a 40 ∈ [0] ∧ a 41 ∈ [0] ∧ a 19 ∈ [0] ∧ a 43 ∈ [0] ∧ a 44 ∈ [0] ∧ a 25 ∈ [0] ∧ a 45 ∈ [0] ∧ a 48 ∈ [0] ∧ a 49 ∈ [0] ∧ a 26 ∈ [0] := by
  have b0 : a 24 ≠ 2 := exclude [0] (fun u v => edge r32 v u) (a 24) (a 11) 2 d11 c32 (by decide +kernel)
  have t0 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b0
  have b1 : a 35 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 35) (a 11) 1 d11 c33 (by decide +kernel)
  have t1 : a 35 ∈ [0] := remove (a 35) 1 [0,1] d35 b1
  have b2 : a 13 ≠ 2 := exclude [0] (edge r38) (a 13) (a 14) 2 d14 c38 (by decide +kernel)
  have t2 : a 13 ∈ [0] := remove (a 13) 2 [0,2] d13 b2
  have b3 : a 39 ≠ 1 := exclude [0] (fun u v => edge r41 v u) (a 39) (a 13) 1 t2 c41 (by decide +kernel)
  have t3 : a 39 ∈ [0] := remove (a 39) 1 [0,1] d39 b3
  have b4 : a 22 ≠ 2 := exclude [0] (fun u v => edge r43 v u) (a 22) (a 14) 2 d14 c43 (by decide +kernel)
  have t4 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b4
  have b5 : a 15 ≠ 1 := exclude [0] (edge r45) (a 15) (a 17) 1 d17 c45 (by decide +kernel)
  have t5 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b5
  have b6 : a 40 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 40) (a 15) 1 t5 c47 (by decide +kernel)
  have t6 : a 40 ∈ [0] := remove (a 40) 1 [0,1] d40 b6
  have b7 : a 41 ≠ 1 := exclude [0] (fun u v => edge r51 v u) (a 41) (a 17) 1 d17 c51 (by decide +kernel)
  have t7 : a 41 ∈ [0] := remove (a 41) 1 [0,1] d41 b7
  have b8 : a 19 ≠ 2 := exclude [0] (edge r54) (a 19) (a 20) 2 d20 c54 (by decide +kernel)
  have t8 : a 19 ∈ [0] := remove (a 19) 2 [0,2] d19 b8
  have b9 : a 43 ≠ 2 := exclude [0] (fun u v => edge r58 v u) (a 43) (a 20) 2 d20 c58 (by decide +kernel)
  have t9 : a 43 ∈ [0] := remove (a 43) 2 [0,2] d43 b9
  have b10 : a 44 ≠ 1 := exclude [0] (fun u v => edge r61 v u) (a 44) (a 21) 1 d21 c61 (by decide +kernel)
  have t10 : a 44 ∈ [0] := remove (a 44) 1 [0,1] d44 b10
  have b11 : a 25 ≠ 2 := exclude [0] (fun u v => edge r62 v u) (a 25) (a 22) 2 t4 c62 (by decide +kernel)
  have t11 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b11
  have b12 : a 45 ≠ 1 := exclude [0] (fun u v => edge r63 v u) (a 45) (a 22) 1 t4 c63 (by decide +kernel)
  have t12 : a 45 ∈ [0] := remove (a 45) 1 [0,1] d45 b12
  have b13 : a 48 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 48) (a 24) 1 t0 c67 (by decide +kernel)
  have t13 : a 48 ∈ [0] := remove (a 48) 1 [0,1] d48 b13
  have b14 : a 49 ≠ 1 := exclude [0] (fun u v => edge r68 v u) (a 49) (a 25) 1 t11 c68 (by decide +kernel)
  have t14 : a 49 ∈ [0] := remove (a 49) 1 [0,1] d49 b14
  have b15 : a 26 ≠ 1 := exclude [0] (edge r69) (a 26) (a 27) 1 d27 c69 (by decide +kernel)
  have t15 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk6 (a : Nat → Nat)
    (d32 : a 32 ∈ [0,1])
    (d27 : a 27 ∈ [0])
    (d28 : a 28 ∈ [0,1])
    (d33 : a 33 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d31 : a 31 ∈ [0])
    (d36 : a 36 ∈ [0,1])
    (d37 : a 37 ∈ [0,2])
    (d39 : a 39 ∈ [0])
    (d38 : a 38 ∈ [0,2])
    (d43 : a 43 ∈ [0])
    (d42 : a 42 ∈ [0,1])
    (d41 : a 41 ∈ [0])
    (d47 : a 47 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d15 : a 15 ∈ [0])
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
    : a 32 ∈ [0] ∧ a 28 ∈ [0] ∧ a 30 ∈ [0] ∧ a 36 ∈ [0] ∧ a 37 ∈ [0] ∧ a 38 ∈ [0] ∧ a 42 ∈ [0] ∧ a 47 ∈ [0] ∧ a 12 ∈ [0] ∧ a 16 ∈ [0] ∧ a 29 ∈ [0] := by
  have b0 : a 32 ≠ 1 := exclude [0] (fun u v => edge r71 v u) (a 32) (a 27) 1 d27 c71 (by decide +kernel)
  have t0 : a 32 ∈ [0] := remove (a 32) 1 [0,1] d32 b0
  have b1 : a 28 ≠ 1 := exclude [0] (edge r73) (a 28) (a 33) 1 d33 c73 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b1
  have b2 : a 30 ≠ 1 := exclude [0] (edge r76) (a 30) (a 31) 1 d31 c76 (by decide +kernel)
  have t2 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b2
  have b3 : a 36 ≠ 1 := exclude [0] (fun u v => edge r81 v u) (a 36) (a 32) 1 t0 c81 (by decide +kernel)
  have t3 : a 36 ∈ [0] := remove (a 36) 1 [0,1] d36 b3
  have b4 : a 37 ≠ 2 := exclude [0] (edge r92) (a 37) (a 39) 2 d39 c92 (by decide +kernel)
  have t4 : a 37 ∈ [0] := remove (a 37) 2 [0,2] d37 b4
  have b5 : a 38 ≠ 2 := exclude [0] (edge r94) (a 38) (a 43) 2 d43 c94 (by decide +kernel)
  have t5 : a 38 ∈ [0] := remove (a 38) 2 [0,2] d38 b5
  have b6 : a 42 ≠ 1 := exclude [0] (fun u v => edge r99 v u) (a 42) (a 41) 1 d41 c99 (by decide +kernel)
  have t6 : a 42 ∈ [0] := remove (a 42) 1 [0,1] d42 b6
  have b7 : a 47 ≠ 2 := exclude [0] (fun u v => edge r103 v u) (a 47) (a 43) 2 d43 c103 (by decide +kernel)
  have t7 : a 47 ∈ [0] := remove (a 47) 2 [0,2] d47 b7
  have b8 : a 12 ≠ 1 := exclude [0] (edge r34) (a 12) (a 13) 1 d13 c34 (by decide +kernel)
  have t8 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b8
  have b9 : a 16 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 16) (a 15) 1 d15 c44 (by decide +kernel)
  have t9 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b9
  have b10 : a 29 ≠ 1 := exclude [0] (fun u v => edge r72 v u) (a 29) (a 28) 1 t1 c72 (by decide +kernel)
  have t10 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b10
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (t10))))))))))

theorem chunk7 (a : Nat → Nat)
    (d2 : a 2 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d6 : a 6 ∈ [0,1])
    (d4 : a 4 ∈ [0,2])
    (d14 : a 14 ∈ [0,2])
    (d27 : a 27 ∈ [0,1])
    (d3 : a 3 ∈ [0,2])
    (d11 : a 11 ∈ [0,2])
    (d17 : a 17 ∈ [0,1])
    (d10 : a 10 ∈ [0,2])
    (d20 : a 20 ∈ [0,2])
    (d31 : a 31 ∈ [0,1])
    (d7 : a 7 ∈ [0,2])
    (d21 : a 21 ∈ [0,1])
    (d9 : a 9 ∈ [0,2])
    (d23 : a 23 ∈ [0,2])
    (d33 : a 33 ∈ [0,1])
    (c3 : edge r3 (a 1) (a 2)=true)
    (c4 : edge r4 (a 1) (a 6)=true)
    (c5 : edge r5 (a 2) (a 4)=true)
    (c7 : edge r7 (a 2) (a 14)=true)
    (c8 : edge r8 (a 2) (a 27)=true)
    (c9 : edge r9 (a 3) (a 4)=true)
    (c10 : edge r10 (a 3) (a 11)=true)
    (c11 : edge r11 (a 3) (a 17)=true)
    (c19 : edge r19 (a 6) (a 10)=true)
    (c20 : edge r20 (a 6) (a 20)=true)
    (c21 : edge r21 (a 6) (a 31)=true)
    (c23 : edge r23 (a 7) (a 11)=true)
    (c24 : edge r24 (a 7) (a 21)=true)
    (c27 : edge r27 (a 9) (a 10)=true)
    (c29 : edge r29 (a 9) (a 23)=true)
    (c30 : edge r30 (a 9) (a 33)=true)
    : a 2 ∈ [1] ∧ a 6 ∈ [1] ∧ a 4 ∈ [2] ∧ a 14 ∈ [2] ∧ a 27 ∈ [1] ∧ a 3 ∈ [2] ∧ a 11 ∈ [2] ∧ a 17 ∈ [1] ∧ a 10 ∈ [2] ∧ a 20 ∈ [2] ∧ a 31 ∈ [1] ∧ a 7 ∈ [2] ∧ a 21 ∈ [1] ∧ a 9 ∈ [2] ∧ a 23 ∈ [2] ∧ a 33 ∈ [1] := by
  have b0 : a 2 ≠ 0 := exclude [1] (fun u v => edge r3 v u) (a 2) (a 1) 0 d1 c3 (by decide +kernel)
  have t0 : a 2 ∈ [1] := remove (a 2) 0 [0,1] d2 b0
  have b1 : a 6 ≠ 0 := exclude [1] (fun u v => edge r4 v u) (a 6) (a 1) 0 d1 c4 (by decide +kernel)
  have t1 : a 6 ∈ [1] := remove (a 6) 0 [0,1] d6 b1
  have b2 : a 4 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 4) (a 2) 0 t0 c5 (by decide +kernel)
  have t2 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b2
  have b3 : a 14 ≠ 0 := exclude [1] (fun u v => edge r7 v u) (a 14) (a 2) 0 t0 c7 (by decide +kernel)
  have t3 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b3
  have b4 : a 27 ≠ 0 := exclude [1] (fun u v => edge r8 v u) (a 27) (a 2) 0 t0 c8 (by decide +kernel)
  have t4 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b4
  have b5 : a 3 ≠ 0 := exclude [2] (edge r9) (a 3) (a 4) 0 t2 c9 (by decide +kernel)
  have t5 : a 3 ∈ [2] := remove (a 3) 0 [0,2] d3 b5
  have b6 : a 11 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 11) (a 3) 0 t5 c10 (by decide +kernel)
  have t6 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b6
  have b7 : a 17 ≠ 0 := exclude [2] (fun u v => edge r11 v u) (a 17) (a 3) 0 t5 c11 (by decide +kernel)
  have t7 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b7
  have b8 : a 10 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 10) (a 6) 0 t1 c19 (by decide +kernel)
  have t8 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b8
  have b9 : a 20 ≠ 0 := exclude [1] (fun u v => edge r20 v u) (a 20) (a 6) 0 t1 c20 (by decide +kernel)
  have t9 : a 20 ∈ [2] := remove (a 20) 0 [0,2] d20 b9
  have b10 : a 31 ≠ 0 := exclude [1] (fun u v => edge r21 v u) (a 31) (a 6) 0 t1 c21 (by decide +kernel)
  have t10 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b10
  have b11 : a 7 ≠ 0 := exclude [2] (edge r23) (a 7) (a 11) 0 t6 c23 (by decide +kernel)
  have t11 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b11
  have b12 : a 21 ≠ 0 := exclude [2] (fun u v => edge r24 v u) (a 21) (a 7) 0 t11 c24 (by decide +kernel)
  have t12 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b12
  have b13 : a 9 ≠ 0 := exclude [2] (edge r27) (a 9) (a 10) 0 t8 c27 (by decide +kernel)
  have t13 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b13
  have b14 : a 23 ≠ 0 := exclude [2] (fun u v => edge r29 v u) (a 23) (a 9) 0 t13 c29 (by decide +kernel)
  have t14 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b14
  have b15 : a 33 ≠ 0 := exclude [2] (fun u v => edge r30 v u) (a 33) (a 9) 0 t13 c30 (by decide +kernel)
  have t15 : a 33 ∈ [1] := remove (a 33) 0 [0,1] d33 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_236
