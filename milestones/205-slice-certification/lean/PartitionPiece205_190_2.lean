import PartitionData205_190
namespace PartitionCover205_190
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,6])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,6])
    (d19 : a 19 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d14 : a 14 ∈ [0,6])
    (d15 : a 15 ∈ [0,6])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d24 : a 24 ∈ [0,4])
    (d9 : a 9 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    : a 3 ∈ [0] ∧ a 6 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 11 ∈ [0] ∧ a 19 ∈ [0] ∧ a 4 ∈ [0] ∧ a 20 ∈ [0] ∧ a 14 ∈ [0] ∧ a 15 ∈ [0] ∧ a 23 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0] ∧ a 9 ∈ [0] ∧ a 13 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 6 ≠ 2 := exclude [0] (fun u v => edge r10 v u) (a 6) (a 2) 2 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [0] := remove (a 6) 2 [0,2] d6 b1
  have b2 : a 10 ≠ 6 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 6 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [0] := remove (a 10) 6 [0,6] d10 b2
  have b3 : a 7 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 1 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b3
  have b4 : a 11 ≠ 6 := exclude [0] (fun u v => edge r14 v u) (a 11) (a 3) 6 t0 c14 (by decide +kernel)
  have t4 : a 11 ∈ [0] := remove (a 11) 6 [0,6] d11 b4
  have b5 : a 19 ≠ 1 := exclude [0] (fun u v => edge r15 v u) (a 19) (a 3) 1 t0 c15 (by decide +kernel)
  have t5 : a 19 ∈ [0] := remove (a 19) 1 [0,1] d19 b5
  have b6 : a 4 ≠ 1 := exclude [0] (edge r17) (a 4) (a 6) 1 t1 c17 (by decide +kernel)
  have t6 : a 4 ∈ [0] := remove (a 4) 1 [0,1] d4 b6
  have b7 : a 20 ≠ 1 := exclude [0] (fun u v => edge r19 v u) (a 20) (a 4) 1 t6 c19 (by decide +kernel)
  have t7 : a 20 ∈ [0] := remove (a 20) 1 [0,1] d20 b7
  have b8 : a 14 ≠ 6 := exclude [0] (fun u v => edge r24 v u) (a 14) (a 6) 6 t1 c24 (by decide +kernel)
  have t8 : a 14 ∈ [0] := remove (a 14) 6 [0,6] d14 b8
  have b9 : a 15 ≠ 6 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 6 t3 c26 (by decide +kernel)
  have t9 : a 15 ∈ [0] := remove (a 15) 6 [0,6] d15 b9
  have b10 : a 23 ≠ 1 := exclude [0] (fun u v => edge r27 v u) (a 23) (a 7) 1 t3 c27 (by decide +kernel)
  have t10 : a 23 ∈ [0] := remove (a 23) 1 [0,1] d23 b10
  have b11 : a 8 ≠ 1 := exclude [0] (edge r29) (a 8) (a 10) 1 t2 c29 (by decide +kernel)
  have t11 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b11
  have b12 : a 12 ≠ 1 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 1 t11 c30 (by decide +kernel)
  have t12 : a 12 ∈ [0] := remove (a 12) 1 [0,1] d12 b12
  have b13 : a 24 ≠ 4 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 4 t11 c31 (by decide +kernel)
  have t13 : a 24 ∈ [0] := remove (a 24) 4 [0,4] d24 b13
  have b14 : a 9 ≠ 1 := exclude [0] (edge r32) (a 9) (a 11) 1 t4 c32 (by decide +kernel)
  have t14 : a 9 ∈ [0] := remove (a 9) 1 [0,1] d9 b14
  have b15 : a 13 ≠ 1 := exclude [0] (fun u v => edge r33 v u) (a 13) (a 9) 1 t14 c33 (by decide +kernel)
  have t15 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,8])
    (d9 : a 9 ∈ [0])
    (d26 : a 26 ∈ [0,1])
    (d10 : a 10 ∈ [0])
    (d27 : a 27 ∈ [0,1])
    (d11 : a 11 ∈ [0])
    (d29 : a 29 ∈ [0,8])
    (d13 : a 13 ∈ [0])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [0])
    (d31 : a 31 ∈ [0,3])
    (d15 : a 15 ∈ [0])
    (d16 : a 16 ∈ [0,2])
    (d20 : a 20 ∈ [0])
    (d21 : a 21 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 25 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 29 ∈ [0] ∧ a 30 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 21 ∈ [0] ∧ a 5 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 25 ≠ 8 := exclude [0] (fun u v => edge r34 v u) (a 25) (a 9) 8 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [0] := remove (a 25) 8 [0,8] d25 b0
  have b1 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [0] := remove (a 26) 1 [0,1] d26 b1
  have b2 : a 27 ≠ 1 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0] := remove (a 27) 1 [0,1] d27 b2
  have b3 : a 29 ≠ 8 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 8 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [0] := remove (a 29) 8 [0,8] d29 b3
  have b4 : a 30 ≠ 1 := exclude [0] (fun u v => edge r46 v u) (a 30) (a 14) 1 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [0] := remove (a 30) 1 [0,1] d30 b4
  have b5 : a 31 ≠ 3 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 3 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [0] := remove (a 31) 3 [0,3] d31 b5
  have b6 : a 16 ≠ 2 := exclude [0] (edge r50) (a 16) (a 20) 2 d20 c50 (by decide +kernel)
  have t6 : a 16 ∈ [0] := remove (a 16) 2 [0,2] d16 b6
  have b7 : a 21 ≠ 2 := exclude [0] (fun u v => edge r60 v u) (a 21) (a 20) 2 d20 c60 (by decide +kernel)
  have t7 : a 21 ∈ [0] := remove (a 21) 2 [0,2] d21 b7
  have b8 : a 5 ≠ 1 := exclude [0] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t8 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b8
  have b9 : a 17 ≠ 2 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 2 t6 c48 (by decide +kernel)
  have t9 : a 17 ∈ [0] := remove (a 17) 2 [0,2] d17 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))

theorem chunk10 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [2])
    (d6 : a 6 ∈ [0,2])
    (d10 : a 10 ∈ [0,6])
    (d7 : a 7 ∈ [0,1])
    (d11 : a 11 ∈ [0,6])
    (d19 : a 19 ∈ [0,1])
    (d4 : a 4 ∈ [0,1])
    (d20 : a 20 ∈ [0,1])
    (d14 : a 14 ∈ [0,6])
    (d15 : a 15 ∈ [0,6])
    (d23 : a 23 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,1])
    (d24 : a 24 ∈ [0,4])
    (d9 : a 9 ∈ [0,1])
    (d13 : a 13 ∈ [0,1])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c10 : edge r10 (a 2) (a 6)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c14 : edge r14 (a 3) (a 11)=true)
    (c15 : edge r15 (a 3) (a 19)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c27 : edge r27 (a 7) (a 23)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    : a 3 ∈ [1] ∧ a 6 ∈ [2] ∧ a 10 ∈ [6] ∧ a 7 ∈ [1] ∧ a 11 ∈ [6] ∧ a 19 ∈ [1] ∧ a 4 ∈ [1] ∧ a 20 ∈ [1] ∧ a 14 ∈ [6] ∧ a 15 ∈ [6] ∧ a 23 ∈ [1] ∧ a 8 ∈ [1] ∧ a 12 ∈ [1] ∧ a 24 ∈ [4] ∧ a 9 ∈ [1] ∧ a 13 ∈ [1] := by
  have b0 : a 3 ≠ 0 := exclude [2] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 6 ≠ 0 := exclude [2] (fun u v => edge r10 v u) (a 6) (a 2) 0 d2 c10 (by decide +kernel)
  have t1 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b1
  have b2 : a 10 ≠ 0 := exclude [2] (fun u v => edge r11 v u) (a 10) (a 2) 0 d2 c11 (by decide +kernel)
  have t2 : a 10 ∈ [6] := remove (a 10) 0 [0,6] d10 b2
  have b3 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t3 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b3
  have b4 : a 11 ≠ 0 := exclude [1] (fun u v => edge r14 v u) (a 11) (a 3) 0 t0 c14 (by decide +kernel)
  have t4 : a 11 ∈ [6] := remove (a 11) 0 [0,6] d11 b4
  have b5 : a 19 ≠ 0 := exclude [1] (fun u v => edge r15 v u) (a 19) (a 3) 0 t0 c15 (by decide +kernel)
  have t5 : a 19 ∈ [1] := remove (a 19) 0 [0,1] d19 b5
  have b6 : a 4 ≠ 0 := exclude [2] (edge r17) (a 4) (a 6) 0 t1 c17 (by decide +kernel)
  have t6 : a 4 ∈ [1] := remove (a 4) 0 [0,1] d4 b6
  have b7 : a 20 ≠ 0 := exclude [1] (fun u v => edge r19 v u) (a 20) (a 4) 0 t6 c19 (by decide +kernel)
  have t7 : a 20 ∈ [1] := remove (a 20) 0 [0,1] d20 b7
  have b8 : a 14 ≠ 0 := exclude [2] (fun u v => edge r24 v u) (a 14) (a 6) 0 t1 c24 (by decide +kernel)
  have t8 : a 14 ∈ [6] := remove (a 14) 0 [0,6] d14 b8
  have b9 : a 15 ≠ 0 := exclude [1] (fun u v => edge r26 v u) (a 15) (a 7) 0 t3 c26 (by decide +kernel)
  have t9 : a 15 ∈ [6] := remove (a 15) 0 [0,6] d15 b9
  have b10 : a 23 ≠ 0 := exclude [1] (fun u v => edge r27 v u) (a 23) (a 7) 0 t3 c27 (by decide +kernel)
  have t10 : a 23 ∈ [1] := remove (a 23) 0 [0,1] d23 b10
  have b11 : a 8 ≠ 0 := exclude [6] (edge r29) (a 8) (a 10) 0 t2 c29 (by decide +kernel)
  have t11 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b11
  have b12 : a 12 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 12) (a 8) 0 t11 c30 (by decide +kernel)
  have t12 : a 12 ∈ [1] := remove (a 12) 0 [0,1] d12 b12
  have b13 : a 24 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 24) (a 8) 0 t11 c31 (by decide +kernel)
  have t13 : a 24 ∈ [4] := remove (a 24) 0 [0,4] d24 b13
  have b14 : a 9 ≠ 0 := exclude [6] (edge r32) (a 9) (a 11) 0 t4 c32 (by decide +kernel)
  have t14 : a 9 ∈ [1] := remove (a 9) 0 [0,1] d9 b14
  have b15 : a 13 ≠ 0 := exclude [1] (fun u v => edge r33 v u) (a 13) (a 9) 0 t14 c33 (by decide +kernel)
  have t15 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk11 (a : Nat → Nat)
    (d25 : a 25 ∈ [0,8])
    (d9 : a 9 ∈ [1])
    (d26 : a 26 ∈ [0,1])
    (d10 : a 10 ∈ [6])
    (d27 : a 27 ∈ [0,1])
    (d11 : a 11 ∈ [6])
    (d29 : a 29 ∈ [0,8])
    (d13 : a 13 ∈ [1])
    (d30 : a 30 ∈ [0,1])
    (d14 : a 14 ∈ [6])
    (d31 : a 31 ∈ [0,3])
    (d15 : a 15 ∈ [6])
    (d16 : a 16 ∈ [0,2])
    (d20 : a 20 ∈ [1])
    (d21 : a 21 ∈ [0,2])
    (d5 : a 5 ∈ [0,1])
    (d17 : a 17 ∈ [0,2])
    (c21 : edge r21 (a 5) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c60 : edge r60 (a 20) (a 21)=true)
    : a 25 ∈ [8] ∧ a 26 ∈ [1] ∧ a 27 ∈ [1] ∧ a 29 ∈ [8] ∧ a 30 ∈ [1] ∧ a 31 ∈ [3] ∧ a 16 ∈ [2] ∧ a 21 ∈ [2] ∧ a 5 ∈ [1] ∧ a 17 ∈ [2] := by
  have b0 : a 25 ≠ 0 := exclude [1] (fun u v => edge r34 v u) (a 25) (a 9) 0 d9 c34 (by decide +kernel)
  have t0 : a 25 ∈ [8] := remove (a 25) 0 [0,8] d25 b0
  have b1 : a 26 ≠ 0 := exclude [6] (fun u v => edge r37 v u) (a 26) (a 10) 0 d10 c37 (by decide +kernel)
  have t1 : a 26 ∈ [1] := remove (a 26) 0 [0,1] d26 b1
  have b2 : a 27 ≠ 0 := exclude [6] (fun u v => edge r39 v u) (a 27) (a 11) 0 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b2
  have b3 : a 29 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 29) (a 13) 0 d13 c44 (by decide +kernel)
  have t3 : a 29 ∈ [8] := remove (a 29) 0 [0,8] d29 b3
  have b4 : a 30 ≠ 0 := exclude [6] (fun u v => edge r46 v u) (a 30) (a 14) 0 d14 c46 (by decide +kernel)
  have t4 : a 30 ∈ [1] := remove (a 30) 0 [0,1] d30 b4
  have b5 : a 31 ≠ 0 := exclude [6] (fun u v => edge r47 v u) (a 31) (a 15) 0 d15 c47 (by decide +kernel)
  have t5 : a 31 ∈ [3] := remove (a 31) 0 [0,3] d31 b5
  have b6 : a 16 ≠ 0 := exclude [1] (edge r50) (a 16) (a 20) 0 d20 c50 (by decide +kernel)
  have t6 : a 16 ∈ [2] := remove (a 16) 0 [0,2] d16 b6
  have b7 : a 21 ≠ 0 := exclude [1] (fun u v => edge r60 v u) (a 21) (a 20) 0 d20 c60 (by decide +kernel)
  have t7 : a 21 ∈ [2] := remove (a 21) 0 [0,2] d21 b7
  have b8 : a 5 ≠ 0 := exclude [1] (edge r21) (a 5) (a 13) 0 d13 c21 (by decide +kernel)
  have t8 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b8
  have b9 : a 17 ≠ 0 := exclude [2] (fun u v => edge r48 v u) (a 17) (a 16) 0 t6 c48 (by decide +kernel)
  have t9 : a 17 ∈ [2] := remove (a 17) 0 [0,2] d17 b9
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (t9)))))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_190
