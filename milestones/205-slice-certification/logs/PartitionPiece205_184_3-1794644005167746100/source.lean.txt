import PartitionData205_184
namespace PartitionCover205_184
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d24 : a 24 ∈ [0,3])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0,6])
    (d26 : a 26 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d27 : a 27 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,2])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 11 ∈ [0] ∧ a 14 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0] ∧ a 9 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 15 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 13 ∈ [0] ∧ a 29 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b1
  have b2 : a 10 ≠ 2 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 2 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 2 [0,2] d10 b2
  have b3 : a 11 ≠ 1 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 1 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b3
  have b4 : a 14 ≠ 2 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 2 t1 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0] := remove (a 14) 2 [0,2] d14 b4
  have b5 : a 8 ≠ 2 := exclude [0] (edge r29) (a 8) (a 10) 2 t2 c29 (by decide +kernel)
  have t5 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b5
  have b6 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 t5 c30 (by decide +kernel)
  have t6 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b6
  have b7 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 t5 c31 (by decide +kernel)
  have t7 : a 24 ∈ [0] := remove (a 24) 3 [0,3] d24 b7
  have b8 : a 9 ≠ 1 := exclude [0] (edge r32) (a 9) (a 11) 1 t3 c32 (by decide +kernel)
  have t8 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b8
  have b9 : a 25 ≠ 6 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 6 t8 c34 (by decide +kernel)
  have t9 : a 25 ∈ [0] := remove (a 25) 6 [0,6] d25 b9
  have b10 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t2 c37 (by decide +kernel)
  have t10 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b10
  have b11 : a 15 ≠ 1 := exclude [0] (fun u v => edge r38 v u) (a 15) (a 11) 1 t3 c38 (by decide +kernel)
  have t11 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b11
  have b12 : a 27 ≠ 2 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 2 t3 c39 (by decide +kernel)
  have t12 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b12
  have b13 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t6 c42 (by decide +kernel)
  have t13 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b13
  have b14 : a 13 ≠ 1 := exclude [0] (edge r43) (a 13) (a 15) 1 t11 c43 (by decide +kernel)
  have t14 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b14
  have b15 : a 29 ≠ 2 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 2 t14 c44 (by decide +kernel)
  have t15 : a 29 ∈ [0] := remove (a 29) 2 [0,2] d29 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk13 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,3])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,3])
    (d24 : a 24 ∈ [0])
    (d17 : a 17 ∈ [0,6])
    (d25 : a 25 ∈ [0])
    (d19 : a 19 ∈ [0,2])
    (d27 : a 27 ∈ [0])
    (d23 : a 23 ∈ [0,2])
    (d30 : a 30 ∈ [0,2])
    (d26 : a 26 ∈ [0])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d20 : a 20 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0] ∧ a 19 ∈ [0] ∧ a 23 ∈ [0] ∧ a 30 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 20 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [0] := remove (a 31) 3 [0,3] d31 b0
  have b1 : a 16 ≠ 3 := exclude [0] (edge r51) (a 16) (a 24) 3 d24 c51 (by decide +kernel)
  have t1 : a 16 ∈ [0] := remove (a 16) 3 [0,3] d16 b1
  have b2 : a 17 ≠ 6 := exclude [0] (edge r54) (a 17) (a 25) 6 d25 c54 (by decide +kernel)
  have t2 : a 17 ∈ [0] := remove (a 17) 6 [0,6] d17 b2
  have b3 : a 19 ≠ 2 := exclude [0] (edge r59) (a 19) (a 27) 2 d27 c59 (by decide +kernel)
  have t3 : a 19 ∈ [0] := remove (a 19) 2 [0,2] d19 b3
  have b4 : a 23 ≠ 2 := exclude [0] (edge r67) (a 23) (a 31) 2 t0 c67 (by decide +kernel)
  have t4 : a 23 ∈ [0] := remove (a 23) 2 [0,2] d23 b4
  have b5 : a 30 ≠ 2 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 2 d26 c74 (by decide +kernel)
  have t5 : a 30 ∈ [0] := remove (a 30) 2 [0,2] d30 b5
  have b6 : a 4 ≠ 1 := exclude [0] (edge r18) (a 4) (a 12) 1 d12 c18 (by decide +kernel)
  have t6 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b6
  have b7 : a 5 ≠ 1 := exclude [0] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t7 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b7
  have b8 : a 20 ≠ 1 := exclude [0] (fun u v => edge r50 v u) (a 20) (a 16) 1 t1 c50 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b8
  have b9 : a 22 ≠ 2 := exclude [0] (edge r65) (a 22) (a 23) 2 t4 c65 (by decide +kernel)
  have t9 : a 22 ∈ [0] := remove (a 22) 2 [0,2] d22 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))

theorem chunk14 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,2])
    (d11 : a 11 ∈ [0,1])
    (d14 : a 14 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (d12 : a 12 ∈ [0,1])
    (d24 : a 24 ∈ [0,3])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0,6])
    (d26 : a 26 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d27 : a 27 ∈ [0,2])
    (d28 : a 28 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,2])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    : a 3 ∈ [1] ∧ a 6 ∈ [2] ∧ a 10 ∈ [2] ∧ a 11 ∈ [1] ∧ a 14 ∈ [2] ∧ a 8 ∈ [2] ∧ a 12 ∈ [1] ∧ a 24 ∈ [3] ∧ a 9 ∈ [1] ∧ a 25 ∈ [6] ∧ a 26 ∈ [1] ∧ a 15 ∈ [1] ∧ a 27 ∈ [2] ∧ a 28 ∈ [1] ∧ a 13 ∈ [1] ∧ a 29 ∈ [2] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 6 ≠ 0 := exclude [1] (fun u v => edge r10 v u) (a 6) (a 2) 0 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b1
  have b2 : a 10 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 10) (a 2) 0 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [2] := remove (a 10) 0 [0,2] d10 b2
  have b3 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t3 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b3
  have b4 : a 14 ≠ 0 := exclude [2] (fun u v => edge r24 v u) (a 14) (a 6) 0 t1 c24 (by decide +kernel)
  have t4 : a 14 ∈ [2] := remove (a 14) 0 [0,2] d14 b4
  have b5 : a 8 ≠ 0 := exclude [2] (edge r29) (a 8) (a 10) 0 t2 c29 (by decide +kernel)
  have t5 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b5
  have b6 : a 12 ≠ 0 := exclude [2] (fun u v => edge r30 v u) (a 12) (a 8) 0 t5 c30 (by decide +kernel)
  have t6 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b6
  have b7 : a 24 ≠ 0 := exclude [2] (fun u v => edge r31 v u) (a 24) (a 8) 0 t5 c31 (by decide +kernel)
  have t7 : a 24 ∈ [3] := remove (a 24) 0 [0,3] d24 b7
  have b8 : a 9 ≠ 0 := exclude [1] (edge r32) (a 9) (a 11) 0 t3 c32 (by decide +kernel)
  have t8 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b8
  have b9 : a 25 ≠ 0 := exclude [1] (fun u v => edge r34 v u) (a 25) (a 9) 0 t8 c34 (by decide +kernel)
  have t9 : a 25 ∈ [6] := remove (a 25) 0 [0,6] d25 b9
  have b10 : a 26 ≠ 0 := exclude [2] (fun u v => edge r37 v u) (a 26) (a 10) 0 t2 c37 (by decide +kernel)
  have t10 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b10
  have b11 : a 15 ≠ 0 := exclude [1] (fun u v => edge r38 v u) (a 15) (a 11) 0 t3 c38 (by decide +kernel)
  have t11 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b11
  have b12 : a 27 ≠ 0 := exclude [1] (fun u v => edge r39 v u) (a 27) (a 11) 0 t3 c39 (by decide +kernel)
  have t12 : a 27 ∈ [2] := remove (a 27) 0 [0,2] d27 b12
  have b13 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 t6 c42 (by decide +kernel)
  have t13 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b13
  have b14 : a 13 ≠ 0 := exclude [1] (edge r43) (a 13) (a 15) 0 t11 c43 (by decide +kernel)
  have t14 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b14
  have b15 : a 29 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 29) (a 13) 0 t14 c44 (by decide +kernel)
  have t15 : a 29 ∈ [2] := remove (a 29) 0 [0,2] d29 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d31 : a 31 ∈ [0,3])
    (d15 : a 15 ∈ [1])
    (d16 : a 16 ∈ [0,3])
    (d24 : a 24 ∈ [3])
    (d17 : a 17 ∈ [0,6])
    (d25 : a 25 ∈ [6])
    (d19 : a 19 ∈ [0,2])
    (d27 : a 27 ∈ [2])
    (d23 : a 23 ∈ [0,2])
    (d30 : a 30 ∈ [0,2])
    (d26 : a 26 ∈ [1])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [1])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [1])
    (d20 : a 20 ∈ [0,1])
    (d22 : a 22 ∈ [0,2])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c54 : edge r54 (a 17) (a 25)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 31 ∈ [3] ∧ a 16 ∈ [3] ∧ a 17 ∈ [6] ∧ a 19 ∈ [2] ∧ a 23 ∈ [2] ∧ a 30 ∈ [2] ∧ a 4 ∈ [1] ∧ a 5 ∈ [1] ∧ a 20 ∈ [1] ∧ a 22 ∈ [2] := by
  have b0 : a 31 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 31) (a 15) 0 d15 c47 (by decide +kernel)
  have t0 : a 31 ∈ [3] := remove (a 31) 0 [0,3] d31 b0
  have b1 : a 16 ≠ 0 := exclude [3] (edge r51) (a 16) (a 24) 0 d24 c51 (by decide +kernel)
  have t1 : a 16 ∈ [3] := remove (a 16) 0 [0,3] d16 b1
  have b2 : a 17 ≠ 0 := exclude [6] (edge r54) (a 17) (a 25) 0 d25 c54 (by decide +kernel)
  have t2 : a 17 ∈ [6] := remove (a 17) 0 [0,6] d17 b2
  have b3 : a 19 ≠ 0 := exclude [2] (edge r59) (a 19) (a 27) 0 d27 c59 (by decide +kernel)
  have t3 : a 19 ∈ [2] := remove (a 19) 0 [0,2] d19 b3
  have b4 : a 23 ≠ 0 := exclude [3] (edge r67) (a 23) (a 31) 0 t0 c67 (by decide +kernel)
  have t4 : a 23 ∈ [2] := remove (a 23) 0 [0,2] d23 b4
  have b5 : a 30 ≠ 0 := exclude [1] (fun u v => edge r74 v u) (a 30) (a 26) 0 d26 c74 (by decide +kernel)
  have t5 : a 30 ∈ [2] := remove (a 30) 0 [0,2] d30 b5
  have b6 : a 4 ≠ 0 := exclude [1] (edge r18) (a 4) (a 12) 0 d12 c18 (by decide +kernel)
  have t6 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b6
  have b7 : a 5 ≠ 0 := exclude [1] (edge r21) (a 5) (a 13) 0 d13 c21 (by decide +kernel)
  have t7 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b7
  have b8 : a 20 ≠ 0 := exclude [3] (fun u v => edge r50 v u) (a 20) (a 16) 0 t1 c50 (by decide +kernel)
  have t8 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b8
  have b9 : a 22 ≠ 0 := exclude [2] (edge r65) (a 22) (a 23) 0 t4 c65 (by decide +kernel)
  have t9 : a 22 ∈ [2] := remove (a 22) 0 [0,2] d22 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_184
