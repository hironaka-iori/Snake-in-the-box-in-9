import PartitionData205_207
namespace PartitionCover205_207
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [0])
    (d2 : a 2 ∈ [0,3])
    (d6 : a 6 ∈ [0,3])
    (d7 : a 7 ∈ [0,3])
    (d11 : a 11 ∈ [0,2])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 3 ∈ [0] ∧ a 2 ∈ [0] ∧ a 6 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 4 ∈ [0] ∧ a 12 ∈ [0] ∧ a 20 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] ∧ a 28 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r5 v u) (a 3) (a 1) 1 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 2 ≠ 3 := exclude [0] (edge r9) (a 2) (a 3) 3 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [0] := remove (a 2) 3 [0,3] d2 b1
  have b2 : a 6 ≠ 3 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 3 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [0] := remove (a 6) 3 [0,3] d6 b2
  have b3 : a 7 ≠ 3 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 3 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 3 [0,3] d7 b3
  have b4 : a 11 ≠ 2 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 2 t0 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 2 [0,2] d11 b4
  have b5 : a 19 ≠ 6 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 6 t0 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0] := remove (a 19) 6 [0,6] d19 b5
  have b6 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t2 c17 (by decide +kernel)
  have t6 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b6
  have b7 : a 12 ≠ 1 := exclude [0] (fun u v => edge r18 v u) (a 12) (a 4) 1 t6 c18 (by decide +kernel)
  have t7 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b7
  have b8 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 t6 c19 (by decide +kernel)
  have t8 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b8
  have b9 : a 14 ≠ 1 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 1 t2 c24 (by decide +kernel)
  have t9 : a 14 ∈ [0] := remove (a 14) 1 [0,1] d14 b9
  have b10 : a 15 ≠ 2 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 2 t3 c26 (by decide +kernel)
  have t10 : a 15 ∈ [0] := remove (a 15) 2 [0,2] d15 b10
  have b11 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 t3 c27 (by decide +kernel)
  have t11 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b11
  have b12 : a 8 ≠ 2 := exclude [0] (edge r30) (a 8) (a 12) 2 t7 c30 (by decide +kernel)
  have t12 : a 8 ∈ [0] := remove (a 8) 2 [0,2] d8 b12
  have b13 : a 9 ≠ 2 := exclude [0] (edge r32) (a 9) (a 11) 2 t4 c32 (by decide +kernel)
  have t13 : a 9 ∈ [0] := remove (a 9) 2 [0,2] d9 b13
  have b14 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 t13 c33 (by decide +kernel)
  have t14 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b14
  have b15 : a 28 ≠ 1 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 1 t7 c42 (by decide +kernel)
  have t15 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk13 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d17 : a 17 ∈ [0,1])
    (d19 : a 19 ∈ [0])
    (d21 : a 21 ∈ [0,1])
    (d25 : a 25 ∈ [0,2])
    (d26 : a 26 ∈ [0,1])
    (d27 : a 27 ∈ [0,2])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 17 ∈ [0] ∧ a 21 ∈ [0] ∧ a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] := by
  have b0 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b0
  have b1 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b1
  have b2 : a 31 ≠ 1 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b2
  have b3 : a 16 ≠ 1 := exclude [0] (edge r50) (a 16) (a 20) 1 d20 c50 (by decide +kernel)
  have t3 : a 16 ∈ [0] := remove (a 16) 1 [0,1] d16 b3
  have b4 : a 17 ≠ 1 := exclude [0] (edge r52) (a 17) (a 19) 1 d19 c52 (by decide +kernel)
  have t4 : a 17 ∈ [0] := remove (a 17) 1 [0,1] d17 b4
  have b5 : a 21 ≠ 1 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 1 d20 c60 (by decide +kernel)
  have t5 : a 21 ∈ [0] := remove (a 21) 1 [0,1] d21 b5
  have b6 : a 25 ≠ 2 := exclude [0] (edge r72) (a 25) (a 29) 2 t0 c72 (by decide +kernel)
  have t6 : a 25 ∈ [0] := remove (a 25) 2 [0,2] d25 b6
  have b7 : a 26 ≠ 1 := exclude [0] (edge r74) (a 26) (a 30) 1 t1 c74 (by decide +kernel)
  have t7 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b7
  have b8 : a 27 ≠ 2 := exclude [0] (fun u v => edge r71 v u) (a 27) (a 25) 2 t6 c71 (by decide +kernel)
  have t8 : a 27 ∈ [0] := remove (a 27) 2 [0,2] d27 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))

theorem chunk14 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d1 : a 1 ∈ [1])
    (d2 : a 2 ∈ [0,3])
    (d6 : a 6 ∈ [0,3])
    (d7 : a 7 ∈ [0,3])
    (d11 : a 11 ∈ [0,2])
    (d19 : a 19 ∈ [0,6])
    (d4 : a 4 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d14 : a 14 ∈ [0,1])
    (d15 : a 15 ∈ [0,2])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,2])
    (d9 : a 9 ∈ [0,2])
    (d13 : a 13 ∈ [0,1])
    (d28 : a 28 ∈ [0,1])
    (c5 : edge r5 (a 1) (a 3)=true)
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c18 : edge r18 (a 4) (a 12)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    : a 3 ∈ [1] ∧ a 2 ∈ [3] ∧ a 6 ∈ [3] ∧ a 7 ∈ [3] ∧ a 11 ∈ [2] ∧ a 19 ∈ [6] ∧ a 4 ∈ [1] ∧ a 12 ∈ [1] ∧ a 20 ∈ [1] ∧ a 14 ∈ [1] ∧ a 15 ∈ [2] ∧ a 23 ∈ [1] ∧ a 8 ∈ [2] ∧ a 9 ∈ [2] ∧ a 13 ∈ [1] ∧ a 28 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r5 v u) (a 3) (a 1) 0 d1 c5 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 2 ≠ 0 := exclude [1] (edge r9) (a 2) (a 3) 0 t0 c9 (by decide +kernel)
  have t1 : a 2 ∈ [3] := remove (a 2) 0 [0,3] d2 b1
  have b2 : a 6 ≠ 0 := exclude [3] (fun u v => edge r10 v u) (a 6) (a 2) 0 t1 c10 (by decide +kernel)
  have t2 : a 6 ∈ [3] := remove (a 6) 0 [0,3] d6 b2
  have b3 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [3] := remove (a 7) 0 [0,3] d7 b3
  have b4 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t4 : a 11 ∈ [2] := remove (a 11) 0 [0,2] d11 b4
  have b5 : a 19 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 19) (a 3) 0 t0 c15 (by decide +kernel)
  have t5 : a 19 ∈ [6] := remove (a 19) 0 [0,6] d19 b5
  have b6 : a 4 ≠ 0 := exclude [3] (edge r17) (a 4) (a 6) 0 t2 c17 (by decide +kernel)
  have t6 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b6
  have b7 : a 12 ≠ 0 := exclude [1] (fun u v => edge r18 v u) (a 12) (a 4) 0 t6 c18 (by decide +kernel)
  have t7 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b7
  have b8 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t6 c19 (by decide +kernel)
  have t8 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b8
  have b9 : a 14 ≠ 0 := exclude [3] (fun u v => edge r24 v u) (a 14) (a 6) 0 t2 c24 (by decide +kernel)
  have t9 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b9
  have b10 : a 15 ≠ 0 := exclude [3] (fun u v => edge r26 v u) (a 15) (a 7) 0 t3 c26 (by decide +kernel)
  have t10 : a 15 ∈ [2] := remove (a 15) 0 [0,2] d15 b10
  have b11 : a 23 ≠ 0 := exclude [3] (fun u v => edge r27 v u) (a 23) (a 7) 0 t3 c27 (by decide +kernel)
  have t11 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b11
  have b12 : a 8 ≠ 0 := exclude [1] (edge r30) (a 8) (a 12) 0 t7 c30 (by decide +kernel)
  have t12 : a 8 ∈ [2] := remove (a 8) 0 [0,2] d8 b12
  have b13 : a 9 ≠ 0 := exclude [2] (edge r32) (a 9) (a 11) 0 t4 c32 (by decide +kernel)
  have t13 : a 9 ∈ [2] := remove (a 9) 0 [0,2] d9 b13
  have b14 : a 13 ≠ 0 := exclude [2] (fun u v => edge r33 v u) (a 13) (a 9) 0 t13 c33 (by decide +kernel)
  have t14 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b14
  have b15 : a 28 ≠ 0 := exclude [1] (fun u v => edge r42 v u) (a 28) (a 12) 0 t7 c42 (by decide +kernel)
  have t15 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk15 (a : Nat → Nat)
    (d29 : a 29 ∈ [0,1])
    (d13 : a 13 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [1])
    (d31 : a 31 ∈ [0,1])
    (d15 : a 15 ∈ [2])
    (d16 : a 16 ∈ [0,1])
    (d20 : a 20 ∈ [1])
    (d17 : a 17 ∈ [0,1])
    (d19 : a 19 ∈ [6])
    (d21 : a 21 ∈ [0,1])
    (d25 : a 25 ∈ [0,2])
    (d26 : a 26 ∈ [0,1])
    (d27 : a 27 ∈ [0,2])
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    (c71 : edge r71 (a 25) (a 27)=true)
    (c72 : edge r72 (a 25) (a 29)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 29 ∈ [1] ∧ a 30 ∈ [1] ∧ a 31 ∈ [1] ∧ a 16 ∈ [1] ∧ a 17 ∈ [1] ∧ a 21 ∈ [1] ∧ a 25 ∈ [2] ∧ a 26 ∈ [1] ∧ a 27 ∈ [2] := by
  have b0 : a 29 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 29) (a 13) 0 d13 c44 (by decide +kernel)
  have t0 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b0
  have b1 : a 30 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t1 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b1
  have b2 : a 31 ≠ 0 := exclude [2] (fun u v => edge r47 v u) (a 31) (a 15) 0 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [1] := remove (a 31) 0 [0,1] d31 b2
  have b3 : a 16 ≠ 0 := exclude [1] (edge r50) (a 16) (a 20) 0 d20 c50 (by decide +kernel)
  have t3 : a 16 ∈ [1] := remove (a 16) 0 [0,1] d16 b3
  have b4 : a 17 ≠ 0 := exclude [6] (edge r52) (a 17) (a 19) 0 d19 c52 (by decide +kernel)
  have t4 : a 17 ∈ [1] := remove (a 17) 0 [0,1] d17 b4
  have b5 : a 21 ≠ 0 := exclude [1] (fun u v => edge r60 v u) (a 21) (a 20) 0 d20 c60 (by decide +kernel)
  have t5 : a 21 ∈ [1] := remove (a 21) 0 [0,1] d21 b5
  have b6 : a 25 ≠ 0 := exclude [1] (edge r72) (a 25) (a 29) 0 t0 c72 (by decide +kernel)
  have t6 : a 25 ∈ [2] := remove (a 25) 0 [0,2] d25 b6
  have b7 : a 26 ≠ 0 := exclude [1] (edge r74) (a 26) (a 30) 0 t1 c74 (by decide +kernel)
  have t7 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b7
  have b8 : a 27 ≠ 0 := exclude [2] (fun u v => edge r71 v u) (a 27) (a 25) 0 t6 c71 (by decide +kernel)
  have t8 : a 27 ∈ [2] := remove (a 27) 0 [0,2] d27 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
#print axioms chunk15
end PartitionCover205_207
