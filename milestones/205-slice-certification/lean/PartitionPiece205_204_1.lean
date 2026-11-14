import PartitionData205_204
namespace PartitionCover205_204
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk4 (a : Nat → Nat)
    (d14 : a 14 ∈ [0,1,4,8,10,11,15,16,17,18,19,20,21,22,23])
    (d6 : a 6 ∈ [0,4])
    (d22 : a 22 ∈ [0,1,2,3,4,5])
    (d15 : a 15 ∈ [0,1,2,3,4,5])
    (d7 : a 7 ∈ [0,2])
    (d9 : a 9 ∈ [0,1,2,4])
    (d8 : a 8 ∈ [0,2])
    (d24 : a 24 ∈ [0,1,2])
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    : a 14 ∈ [0,1,4,8,10,11,20,22] ∧ a 22 ∈ [0,4] ∧ a 15 ∈ [0,1,4,5] ∧ a 9 ∈ [0,1] ∧ a 24 ∈ [0,2] := by
  have b0 : a 14 ≠ 15 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 15 d6 c24 (by decide +kernel)
  have t0 : a 14 ∈ [0,1,4,8,10,11,16,17,18,19,20,21,22,23] := remove (a 14) 15 [0,1,4,8,10,11,15,16,17,18,19,20,21,22,23] d14 b0
  have b1 : a 14 ≠ 16 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 16 d6 c24 (by decide +kernel)
  have t1 : a 14 ∈ [0,1,4,8,10,11,17,18,19,20,21,22,23] := remove (a 14) 16 [0,1,4,8,10,11,16,17,18,19,20,21,22,23] t0 b1
  have b2 : a 14 ≠ 17 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 17 d6 c24 (by decide +kernel)
  have t2 : a 14 ∈ [0,1,4,8,10,11,18,19,20,21,22,23] := remove (a 14) 17 [0,1,4,8,10,11,17,18,19,20,21,22,23] t1 b2
  have b3 : a 14 ≠ 18 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 18 d6 c24 (by decide +kernel)
  have t3 : a 14 ∈ [0,1,4,8,10,11,19,20,21,22,23] := remove (a 14) 18 [0,1,4,8,10,11,18,19,20,21,22,23] t2 b3
  have b4 : a 14 ≠ 19 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 19 d6 c24 (by decide +kernel)
  have t4 : a 14 ∈ [0,1,4,8,10,11,20,21,22,23] := remove (a 14) 19 [0,1,4,8,10,11,19,20,21,22,23] t3 b4
  have b5 : a 14 ≠ 21 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 21 d6 c24 (by decide +kernel)
  have t5 : a 14 ∈ [0,1,4,8,10,11,20,22,23] := remove (a 14) 21 [0,1,4,8,10,11,20,21,22,23] t4 b5
  have b6 : a 14 ≠ 23 := exclude [0,4] (fun u v => edge r24 v u) (a 14) (a 6) 23 d6 c24 (by decide +kernel)
  have t6 : a 14 ∈ [0,1,4,8,10,11,20,22] := remove (a 14) 23 [0,1,4,8,10,11,20,22,23] t5 b6
  have b7 : a 22 ≠ 1 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 1 d6 c25 (by decide +kernel)
  have t7 : a 22 ∈ [0,2,3,4,5] := remove (a 22) 1 [0,1,2,3,4,5] d22 b7
  have b8 : a 22 ≠ 2 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 2 d6 c25 (by decide +kernel)
  have t8 : a 22 ∈ [0,3,4,5] := remove (a 22) 2 [0,2,3,4,5] t7 b8
  have b9 : a 22 ≠ 3 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 3 d6 c25 (by decide +kernel)
  have t9 : a 22 ∈ [0,4,5] := remove (a 22) 3 [0,3,4,5] t8 b9
  have b10 : a 22 ≠ 5 := exclude [0,4] (fun u v => edge r25 v u) (a 22) (a 6) 5 d6 c25 (by decide +kernel)
  have t10 : a 22 ∈ [0,4] := remove (a 22) 5 [0,4,5] t9 b10
  have b11 : a 15 ≠ 2 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 2 d7 c26 (by decide +kernel)
  have t11 : a 15 ∈ [0,1,3,4,5] := remove (a 15) 2 [0,1,2,3,4,5] d15 b11
  have b12 : a 15 ≠ 3 := exclude [0,2] (fun u v => edge r26 v u) (a 15) (a 7) 3 d7 c26 (by decide +kernel)
  have t12 : a 15 ∈ [0,1,4,5] := remove (a 15) 3 [0,1,3,4,5] t11 b12
  have b13 : a 9 ≠ 2 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 2 d8 c28 (by decide +kernel)
  have t13 : a 9 ∈ [0,1,4] := remove (a 9) 2 [0,1,2,4] d9 b13
  have b14 : a 9 ≠ 4 := exclude [0,2] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t14 : a 9 ∈ [0,1] := remove (a 9) 4 [0,1,4] t13 b14
  have b15 : a 24 ≠ 1 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 1 d8 c31 (by decide +kernel)
  have t15 : a 24 ∈ [0,2] := remove (a 24) 1 [0,1,2] d24 b15
  exact And.intro t6 (And.intro t10 (And.intro t12 (And.intro t14 (t15))))

theorem chunk5 (a : Nat → Nat)
    (d24 : a 24 ∈ [0,2])
    (d8 : a 8 ∈ [0,2])
    (d13 : a 13 ∈ [0,1,2,3,4,5])
    (d9 : a 9 ∈ [0,1])
    (d25 : a 25 ∈ [0,1,2])
    (d10 : a 10 ∈ [0,5])
    (d11 : a 11 ∈ [0,6])
    (d14 : a 14 ∈ [0,1,4,8,10,11,20,22])
    (d26 : a 26 ∈ [0,1,2,3,4,5])
    (c31 : edge r31 (a 8) (a 24)=true)
    (c33 : edge r33 (a 9) (a 13)=true)
    (c34 : edge r34 (a 9) (a 25)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    : a 24 ∈ [0] ∧ a 13 ∈ [0,1] ∧ a 25 ∈ [0,1] ∧ a 10 ∈ [0] ∧ a 14 ∈ [0,1] ∧ a 26 ∈ [0,2,5] := by
  have b0 : a 24 ≠ 2 := exclude [0,2] (fun u v => edge r31 v u) (a 24) (a 8) 2 d8 c31 (by decide +kernel)
  have t0 : a 24 ∈ [0] := remove (a 24) 2 [0,2] d24 b0
  have b1 : a 13 ≠ 2 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 2 d9 c33 (by decide +kernel)
  have t1 : a 13 ∈ [0,1,3,4,5] := remove (a 13) 2 [0,1,2,3,4,5] d13 b1
  have b2 : a 13 ≠ 3 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 3 d9 c33 (by decide +kernel)
  have t2 : a 13 ∈ [0,1,4,5] := remove (a 13) 3 [0,1,3,4,5] t1 b2
  have b3 : a 13 ≠ 4 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 4 d9 c33 (by decide +kernel)
  have t3 : a 13 ∈ [0,1,5] := remove (a 13) 4 [0,1,4,5] t2 b3
  have b4 : a 13 ≠ 5 := exclude [0,1] (fun u v => edge r33 v u) (a 13) (a 9) 5 d9 c33 (by decide +kernel)
  have t4 : a 13 ∈ [0,1] := remove (a 13) 5 [0,1,5] t3 b4
  have b5 : a 25 ≠ 2 := exclude [0,1] (fun u v => edge r34 v u) (a 25) (a 9) 2 d9 c34 (by decide +kernel)
  have t5 : a 25 ∈ [0,1] := remove (a 25) 2 [0,1,2] d25 b5
  have b6 : a 10 ≠ 5 := exclude [0,6] (edge r35) (a 10) (a 11) 5 d11 c35 (by decide +kernel)
  have t6 : a 10 ∈ [0] := remove (a 10) 5 [0,5] d10 b6
  have b7 : a 14 ≠ 4 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 4 t6 c36 (by decide +kernel)
  have t7 : a 14 ∈ [0,1,8,10,11,20,22] := remove (a 14) 4 [0,1,4,8,10,11,20,22] d14 b7
  have b8 : a 14 ≠ 8 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 8 t6 c36 (by decide +kernel)
  have t8 : a 14 ∈ [0,1,10,11,20,22] := remove (a 14) 8 [0,1,8,10,11,20,22] t7 b8
  have b9 : a 14 ≠ 10 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 10 t6 c36 (by decide +kernel)
  have t9 : a 14 ∈ [0,1,11,20,22] := remove (a 14) 10 [0,1,10,11,20,22] t8 b9
  have b10 : a 14 ≠ 11 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 11 t6 c36 (by decide +kernel)
  have t10 : a 14 ∈ [0,1,20,22] := remove (a 14) 11 [0,1,11,20,22] t9 b10
  have b11 : a 14 ≠ 20 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 20 t6 c36 (by decide +kernel)
  have t11 : a 14 ∈ [0,1,22] := remove (a 14) 20 [0,1,20,22] t10 b11
  have b12 : a 14 ≠ 22 := exclude [0] (fun u v => edge r36 v u) (a 14) (a 10) 22 t6 c36 (by decide +kernel)
  have t12 : a 14 ∈ [0,1] := remove (a 14) 22 [0,1,22] t11 b12
  have b13 : a 26 ≠ 1 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 1 t6 c37 (by decide +kernel)
  have t13 : a 26 ∈ [0,2,3,4,5] := remove (a 26) 1 [0,1,2,3,4,5] d26 b13
  have b14 : a 26 ≠ 3 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 3 t6 c37 (by decide +kernel)
  have t14 : a 26 ∈ [0,2,4,5] := remove (a 26) 3 [0,2,3,4,5] t13 b14
  have b15 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t6 c37 (by decide +kernel)
  have t15 : a 26 ∈ [0,2,5] := remove (a 26) 4 [0,2,4,5] t14 b15
  exact And.intro t0 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t12 (t15)))))

theorem chunk6 (a : Nat → Nat)
    (d26 : a 26 ∈ [0,2,5])
    (d10 : a 10 ∈ [0])
    (d27 : a 27 ∈ [0,1,2,3,4,5,6,7,8])
    (d11 : a 11 ∈ [0,6])
    (d28 : a 28 ∈ [0,1,2,3,4,5])
    (d12 : a 12 ∈ [0,1])
    (d29 : a 29 ∈ [0,1,2,3,4,5])
    (d13 : a 13 ∈ [0,1])
    (d15 : a 15 ∈ [0,1,4,5])
    (d14 : a 14 ∈ [0,1])
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c45 : edge r45 (a 14) (a 15)=true)
    : a 26 ∈ [0,2] ∧ a 27 ∈ [0,3,4,6] ∧ a 28 ∈ [0,1] ∧ a 29 ∈ [0,1] ∧ a 15 ∈ [0,4] := by
  have b0 : a 26 ≠ 5 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 5 d10 c37 (by decide +kernel)
  have t0 : a 26 ∈ [0,2] := remove (a 26) 5 [0,2,5] d26 b0
  have b1 : a 27 ≠ 1 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 1 d11 c39 (by decide +kernel)
  have t1 : a 27 ∈ [0,2,3,4,5,6,7,8] := remove (a 27) 1 [0,1,2,3,4,5,6,7,8] d27 b1
  have b2 : a 27 ≠ 2 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 2 d11 c39 (by decide +kernel)
  have t2 : a 27 ∈ [0,3,4,5,6,7,8] := remove (a 27) 2 [0,2,3,4,5,6,7,8] t1 b2
  have b3 : a 27 ≠ 5 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 5 d11 c39 (by decide +kernel)
  have t3 : a 27 ∈ [0,3,4,6,7,8] := remove (a 27) 5 [0,3,4,5,6,7,8] t2 b3
  have b4 : a 27 ≠ 7 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 7 d11 c39 (by decide +kernel)
  have t4 : a 27 ∈ [0,3,4,6,8] := remove (a 27) 7 [0,3,4,6,7,8] t3 b4
  have b5 : a 27 ≠ 8 := exclude [0,6] (fun u v => edge r39 v u) (a 27) (a 11) 8 d11 c39 (by decide +kernel)
  have t5 : a 27 ∈ [0,3,4,6] := remove (a 27) 8 [0,3,4,6,8] t4 b5
  have b6 : a 28 ≠ 2 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 2 d12 c42 (by decide +kernel)
  have t6 : a 28 ∈ [0,1,3,4,5] := remove (a 28) 2 [0,1,2,3,4,5] d28 b6
  have b7 : a 28 ≠ 3 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 3 d12 c42 (by decide +kernel)
  have t7 : a 28 ∈ [0,1,4,5] := remove (a 28) 3 [0,1,3,4,5] t6 b7
  have b8 : a 28 ≠ 4 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 4 d12 c42 (by decide +kernel)
  have t8 : a 28 ∈ [0,1,5] := remove (a 28) 4 [0,1,4,5] t7 b8
  have b9 : a 28 ≠ 5 := exclude [0,1] (fun u v => edge r42 v u) (a 28) (a 12) 5 d12 c42 (by decide +kernel)
  have t9 : a 28 ∈ [0,1] := remove (a 28) 5 [0,1,5] t8 b9
  have b10 : a 29 ≠ 2 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 2 d13 c44 (by decide +kernel)
  have t10 : a 29 ∈ [0,1,3,4,5] := remove (a 29) 2 [0,1,2,3,4,5] d29 b10
  have b11 : a 29 ≠ 3 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 3 d13 c44 (by decide +kernel)
  have t11 : a 29 ∈ [0,1,4,5] := remove (a 29) 3 [0,1,3,4,5] t10 b11
  have b12 : a 29 ≠ 4 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 4 d13 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0,1,5] := remove (a 29) 4 [0,1,4,5] t11 b12
  have b13 : a 29 ≠ 5 := exclude [0,1] (fun u v => edge r44 v u) (a 29) (a 13) 5 d13 c44 (by decide +kernel)
  have t13 : a 29 ∈ [0,1] := remove (a 29) 5 [0,1,5] t12 b13
  have b14 : a 15 ≠ 1 := exclude [0,1] (fun u v => edge r45 v u) (a 15) (a 14) 1 d14 c45 (by decide +kernel)
  have t14 : a 15 ∈ [0,4,5] := remove (a 15) 1 [0,1,4,5] d15 b14
  have b15 : a 15 ≠ 5 := exclude [0,1] (fun u v => edge r45 v u) (a 15) (a 14) 5 d14 c45 (by decide +kernel)
  have t15 : a 15 ∈ [0,4] := remove (a 15) 5 [0,4,5] t14 b15
  exact And.intro t0 (And.intro t5 (And.intro t9 (And.intro t13 (t15))))

theorem chunk7 (a : Nat → Nat)
    (d30 : a 30 ∈ [0,1,2])
    (d14 : a 14 ∈ [0,1])
    (d31 : a 31 ∈ [0,1,2])
    (d15 : a 15 ∈ [0,4])
    (d17 : a 17 ∈ [0,1,2,3])
    (d19 : a 19 ∈ [0])
    (d21 : a 21 ∈ [0,1,2,3,4,5])
    (d23 : a 23 ∈ [0,1,2])
    (d22 : a 22 ∈ [0,4])
    (d27 : a 27 ∈ [0,3,4,6])
    (d26 : a 26 ∈ [0,2])
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c52 : edge r52 (a 17) (a 19)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c73 : edge r73 (a 26) (a 27)=true)
    : a 30 ∈ [0,1] ∧ a 31 ∈ [0] ∧ a 17 ∈ [0,2] ∧ a 21 ∈ [0,1] ∧ a 23 ∈ [0,2] ∧ a 27 ∈ [0,4] := by
  have b0 : a 30 ≠ 2 := exclude [0,1] (fun u v => edge r46 v u) (a 30) (a 14) 2 d14 c46 (by decide +kernel)
  have t0 : a 30 ∈ [0,1] := remove (a 30) 2 [0,1,2] d30 b0
  have b1 : a 31 ≠ 1 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 1 d15 c47 (by decide +kernel)
  have t1 : a 31 ∈ [0,2] := remove (a 31) 1 [0,1,2] d31 b1
  have b2 : a 31 ≠ 2 := exclude [0,4] (fun u v => edge r47 v u) (a 31) (a 15) 2 d15 c47 (by decide +kernel)
  have t2 : a 31 ∈ [0] := remove (a 31) 2 [0,2] t1 b2
  have b3 : a 17 ≠ 1 := exclude [0] (edge r52) (a 17) (a 19) 1 d19 c52 (by decide +kernel)
  have t3 : a 17 ∈ [0,2,3] := remove (a 17) 1 [0,1,2,3] d17 b3
  have b4 : a 17 ≠ 3 := exclude [0] (edge r52) (a 17) (a 19) 3 d19 c52 (by decide +kernel)
  have t4 : a 17 ∈ [0,2] := remove (a 17) 3 [0,2,3] t3 b4
  have b5 : a 21 ≠ 2 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 2 t4 c53 (by decide +kernel)
  have t5 : a 21 ∈ [0,1,3,4,5] := remove (a 21) 2 [0,1,2,3,4,5] d21 b5
  have b6 : a 21 ≠ 3 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 3 t4 c53 (by decide +kernel)
  have t6 : a 21 ∈ [0,1,4,5] := remove (a 21) 3 [0,1,3,4,5] t5 b6
  have b7 : a 21 ≠ 4 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 4 t4 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0,1,5] := remove (a 21) 4 [0,1,4,5] t6 b7
  have b8 : a 21 ≠ 5 := exclude [0,2] (fun u v => edge r53 v u) (a 21) (a 17) 5 t4 c53 (by decide +kernel)
  have t8 : a 21 ∈ [0,1] := remove (a 21) 5 [0,1,5] t7 b8
  have b9 : a 23 ≠ 1 := exclude [0,4] (fun u v => edge r65 v u) (a 23) (a 22) 1 d22 c65 (by decide +kernel)
  have t9 : a 23 ∈ [0,2] := remove (a 23) 1 [0,1,2] d23 b9
  have b10 : a 27 ≠ 3 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 3 d26 c73 (by decide +kernel)
  have t10 : a 27 ∈ [0,4,6] := remove (a 27) 3 [0,3,4,6] d27 b10
  have b11 : a 27 ≠ 6 := exclude [0,2] (fun u v => edge r73 v u) (a 27) (a 26) 6 d26 c73 (by decide +kernel)
  have t11 : a 27 ∈ [0,4] := remove (a 27) 6 [0,4,6] t10 b11
  exact And.intro t0 (And.intro t2 (And.intro t4 (And.intro t8 (And.intro t9 (t11)))))

#print axioms chunk4
#print axioms chunk5
#print axioms chunk6
#print axioms chunk7
end PartitionCover205_204
