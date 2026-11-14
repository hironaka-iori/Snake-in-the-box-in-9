import PartitionData205_199
namespace PartitionCover205_199
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk8 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [0])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d24 : a 24 ∈ [0,3])
    (d11 : a 11 ∈ [0,1])
    (d26 : a 26 ∈ [0,4])
    (d27 : a 27 ∈ [0,4])
    (d28 : a 28 ∈ [0,4])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0,2])
    (d16 : a 16 ∈ [0,3])
    (d19 : a 19 ∈ [0,4])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 3 ∈ [0] ∧ a 10 ∈ [0] ∧ a 7 ∈ [0] ∧ a 15 ∈ [0] ∧ a 8 ∈ [0] ∧ a 12 ∈ [0] ∧ a 24 ∈ [0] ∧ a 11 ∈ [0] ∧ a 26 ∈ [0] ∧ a 27 ∈ [0] ∧ a 28 ∈ [0] ∧ a 13 ∈ [0] ∧ a 29 ∈ [0] ∧ a 31 ∈ [0] ∧ a 16 ∈ [0] ∧ a 19 ∈ [0] := by
  have b0 : a 3 ≠ 1 := exclude [0] (fun u v => edge r9 v u) (a 3) (a 2) 1 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [0] := remove (a 3) 1 [0,1] d3 b0
  have b1 : a 10 ≠ 1 := exclude [0] (fun u v => edge r11 v u) (a 10) (a 2) 1 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [0] := remove (a 10) 1 [0,1] d10 b1
  have b2 : a 7 ≠ 1 := exclude [0] (fun u v => edge r13 v u) (a 7) (a 3) 1 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [0] := remove (a 7) 1 [0,1] d7 b2
  have b3 : a 15 ≠ 1 := exclude [0] (fun u v => edge r26 v u) (a 15) (a 7) 1 t2 c26 (by decide +kernel)
  have t3 : a 15 ∈ [0] := remove (a 15) 1 [0,1] d15 b3
  have b4 : a 8 ≠ 1 := exclude [0] (edge r29) (a 8) (a 10) 1 t1 c29 (by decide +kernel)
  have t4 : a 8 ∈ [0] := remove (a 8) 1 [0,1] d8 b4
  have b5 : a 12 ≠ 2 := exclude [0] (fun u v => edge r30 v u) (a 12) (a 8) 2 t4 c30 (by decide +kernel)
  have t5 : a 12 ∈ [0] := remove (a 12) 2 [0,2] d12 b5
  have b6 : a 24 ≠ 3 := exclude [0] (fun u v => edge r31 v u) (a 24) (a 8) 3 t4 c31 (by decide +kernel)
  have t6 : a 24 ∈ [0] := remove (a 24) 3 [0,3] d24 b6
  have b7 : a 11 ≠ 1 := exclude [0] (fun u v => edge r35 v u) (a 11) (a 10) 1 t1 c35 (by decide +kernel)
  have t7 : a 11 ∈ [0] := remove (a 11) 1 [0,1] d11 b7
  have b8 : a 26 ≠ 4 := exclude [0] (fun u v => edge r37 v u) (a 26) (a 10) 4 t1 c37 (by decide +kernel)
  have t8 : a 26 ∈ [0] := remove (a 26) 4 [0,4] d26 b8
  have b9 : a 27 ≠ 4 := exclude [0] (fun u v => edge r39 v u) (a 27) (a 11) 4 t7 c39 (by decide +kernel)
  have t9 : a 27 ∈ [0] := remove (a 27) 4 [0,4] d27 b9
  have b10 : a 28 ≠ 4 := exclude [0] (fun u v => edge r42 v u) (a 28) (a 12) 4 t5 c42 (by decide +kernel)
  have t10 : a 28 ∈ [0] := remove (a 28) 4 [0,4] d28 b10
  have b11 : a 13 ≠ 1 := exclude [0] (edge r43) (a 13) (a 15) 1 t3 c43 (by decide +kernel)
  have t11 : a 13 ∈ [0] := remove (a 13) 1 [0,1] d13 b11
  have b12 : a 29 ≠ 1 := exclude [0] (fun u v => edge r44 v u) (a 29) (a 13) 1 t11 c44 (by decide +kernel)
  have t12 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b12
  have b13 : a 31 ≠ 2 := exclude [0] (fun u v => edge r47 v u) (a 31) (a 15) 2 t3 c47 (by decide +kernel)
  have t13 : a 31 ∈ [0] := remove (a 31) 2 [0,2] d31 b13
  have b14 : a 16 ≠ 3 := exclude [0] (edge r51) (a 16) (a 24) 3 t6 c51 (by decide +kernel)
  have t14 : a 16 ∈ [0] := remove (a 16) 3 [0,3] d16 b14
  have b15 : a 19 ≠ 4 := exclude [0] (edge r59) (a 19) (a 27) 4 t9 c59 (by decide +kernel)
  have t15 : a 19 ∈ [0] := remove (a 19) 4 [0,4] d19 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk9 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,4])
    (d31 : a 31 ∈ [0])
    (d25 : a 25 ∈ [0,6])
    (d24 : a 24 ∈ [0])
    (d30 : a 30 ∈ [0,4])
    (d26 : a 26 ∈ [0])
    (d4 : a 4 ∈ [0,2])
    (d12 : a 12 ∈ [0])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [0])
    (d9 : a 9 ∈ [0,4])
    (d8 : a 8 ∈ [0])
    (d17 : a 17 ∈ [0,6])
    (d16 : a 16 ∈ [0])
    (d21 : a 21 ∈ [0,3])
    (d22 : a 22 ∈ [0,4])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 23 ∈ [0] ∧ a 25 ∈ [0] ∧ a 30 ∈ [0] ∧ a 4 ∈ [0] ∧ a 5 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] ∧ a 21 ∈ [0] ∧ a 22 ∈ [0] := by
  have b0 : a 23 ≠ 4 := exclude [0] (edge r67) (a 23) (a 31) 4 d31 c67 (by decide +kernel)
  have t0 : a 23 ∈ [0] := remove (a 23) 4 [0,4] d23 b0
  have b1 : a 25 ≠ 6 := exclude [0] (fun u v => edge r68 v u) (a 25) (a 24) 6 d24 c68 (by decide +kernel)
  have t1 : a 25 ∈ [0] := remove (a 25) 6 [0,6] d25 b1
  have b2 : a 30 ≠ 4 := exclude [0] (fun u v => edge r74 v u) (a 30) (a 26) 4 d26 c74 (by decide +kernel)
  have t2 : a 30 ∈ [0] := remove (a 30) 4 [0,4] d30 b2
  have b3 : a 4 ≠ 2 := exclude [0] (edge r18) (a 4) (a 12) 2 d12 c18 (by decide +kernel)
  have t3 : a 4 ∈ [0] := remove (a 4) 2 [0,2] d4 b3
  have b4 : a 5 ≠ 1 := exclude [0] (edge r21) (a 5) (a 13) 1 d13 c21 (by decide +kernel)
  have t4 : a 5 ∈ [0] := remove (a 5) 1 [0,1] d5 b4
  have b5 : a 9 ≠ 4 := exclude [0] (fun u v => edge r28 v u) (a 9) (a 8) 4 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [0] := remove (a 9) 4 [0,4] d9 b5
  have b6 : a 17 ≠ 6 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 6 d16 c48 (by decide +kernel)
  have t6 : a 17 ∈ [0] := remove (a 17) 6 [0,6] d17 b6
  have b7 : a 21 ≠ 3 := exclude [0] (fun u v => edge r53 v u) (a 21) (a 17) 3 t6 c53 (by decide +kernel)
  have t7 : a 21 ∈ [0] := remove (a 21) 3 [0,3] d21 b7
  have b8 : a 22 ≠ 4 := exclude [0] (edge r65) (a 22) (a 23) 4 t0 c65 (by decide +kernel)
  have t8 : a 22 ∈ [0] := remove (a 22) 4 [0,4] d22 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))

theorem chunk10 (a : Nat → Nat)
    (d3 : a 3 ∈ [0,1])
    (d2 : a 2 ∈ [1])
    (d10 : a 10 ∈ [0,1])
    (d7 : a 7 ∈ [0,1])
    (d15 : a 15 ∈ [0,1])
    (d8 : a 8 ∈ [0,1])
    (d12 : a 12 ∈ [0,2])
    (d24 : a 24 ∈ [0,3])
    (d11 : a 11 ∈ [0,1])
    (d26 : a 26 ∈ [0,4])
    (d27 : a 27 ∈ [0,4])
    (d28 : a 28 ∈ [0,4])
    (d13 : a 13 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d31 : a 31 ∈ [0,2])
    (d16 : a 16 ∈ [0,3])
    (d19 : a 19 ∈ [0,4])
    (c9 : edge r9 (a 2) (a 3)=true)
    (c11 : edge r11 (a 2) (a 10)=true)
    (c13 : edge r13 (a 3) (a 7)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c29 : edge r29 (a 8) (a 10)=true)
    (c30 : edge r30 (a 8) (a 12)=true)
    (c31 : edge r31 (a 8) (a 24)=true)
    (c35 : edge r35 (a 10) (a 11)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c42 : edge r42 (a 12) (a 28)=true)
    (c43 : edge r43 (a 13) (a 15)=true)
    (c44 : edge r44 (a 13) (a 29)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c51 : edge r51 (a 16) (a 24)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    : a 3 ∈ [1] ∧ a 10 ∈ [1] ∧ a 7 ∈ [1] ∧ a 15 ∈ [1] ∧ a 8 ∈ [1] ∧ a 12 ∈ [2] ∧ a 24 ∈ [3] ∧ a 11 ∈ [1] ∧ a 26 ∈ [4] ∧ a 27 ∈ [4] ∧ a 28 ∈ [4] ∧ a 13 ∈ [1] ∧ a 29 ∈ [1] ∧ a 31 ∈ [2] ∧ a 16 ∈ [3] ∧ a 19 ∈ [4] := by
  have b0 : a 3 ≠ 0 := exclude [1] (fun u v => edge r9 v u) (a 3) (a 2) 0 d2 c9 (by decide +kernel)
  have t0 : a 3 ∈ [1] := remove (a 3) 0 [0,1] d3 b0
  have b1 : a 10 ≠ 0 := exclude [1] (fun u v => edge r11 v u) (a 10) (a 2) 0 d2 c11 (by decide +kernel)
  have t1 : a 10 ∈ [1] := remove (a 10) 0 [0,1] d10 b1
  have b2 : a 7 ≠ 0 := exclude [1] (fun u v => edge r13 v u) (a 7) (a 3) 0 t0 c13 (by decide +kernel)
  have t2 : a 7 ∈ [1] := remove (a 7) 0 [0,1] d7 b2
  have b3 : a 15 ≠ 0 := exclude [1] (fun u v => edge r26 v u) (a 15) (a 7) 0 t2 c26 (by decide +kernel)
  have t3 : a 15 ∈ [1] := remove (a 15) 0 [0,1] d15 b3
  have b4 : a 8 ≠ 0 := exclude [1] (edge r29) (a 8) (a 10) 0 t1 c29 (by decide +kernel)
  have t4 : a 8 ∈ [1] := remove (a 8) 0 [0,1] d8 b4
  have b5 : a 12 ≠ 0 := exclude [1] (fun u v => edge r30 v u) (a 12) (a 8) 0 t4 c30 (by decide +kernel)
  have t5 : a 12 ∈ [2] := remove (a 12) 0 [0,2] d12 b5
  have b6 : a 24 ≠ 0 := exclude [1] (fun u v => edge r31 v u) (a 24) (a 8) 0 t4 c31 (by decide +kernel)
  have t6 : a 24 ∈ [3] := remove (a 24) 0 [0,3] d24 b6
  have b7 : a 11 ≠ 0 := exclude [1] (fun u v => edge r35 v u) (a 11) (a 10) 0 t1 c35 (by decide +kernel)
  have t7 : a 11 ∈ [1] := remove (a 11) 0 [0,1] d11 b7
  have b8 : a 26 ≠ 0 := exclude [1] (fun u v => edge r37 v u) (a 26) (a 10) 0 t1 c37 (by decide +kernel)
  have t8 : a 26 ∈ [4] := remove (a 26) 0 [0,4] d26 b8
  have b9 : a 27 ≠ 0 := exclude [1] (fun u v => edge r39 v u) (a 27) (a 11) 0 t7 c39 (by decide +kernel)
  have t9 : a 27 ∈ [4] := remove (a 27) 0 [0,4] d27 b9
  have b10 : a 28 ≠ 0 := exclude [2] (fun u v => edge r42 v u) (a 28) (a 12) 0 t5 c42 (by decide +kernel)
  have t10 : a 28 ∈ [4] := remove (a 28) 0 [0,4] d28 b10
  have b11 : a 13 ≠ 0 := exclude [1] (edge r43) (a 13) (a 15) 0 t3 c43 (by decide +kernel)
  have t11 : a 13 ∈ [1] := remove (a 13) 0 [0,1] d13 b11
  have b12 : a 29 ≠ 0 := exclude [1] (fun u v => edge r44 v u) (a 29) (a 13) 0 t11 c44 (by decide +kernel)
  have t12 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b12
  have b13 : a 31 ≠ 0 := exclude [1] (fun u v => edge r47 v u) (a 31) (a 15) 0 t3 c47 (by decide +kernel)
  have t13 : a 31 ∈ [2] := remove (a 31) 0 [0,2] d31 b13
  have b14 : a 16 ≠ 0 := exclude [3] (edge r51) (a 16) (a 24) 0 t6 c51 (by decide +kernel)
  have t14 : a 16 ∈ [3] := remove (a 16) 0 [0,3] d16 b14
  have b15 : a 19 ≠ 0 := exclude [4] (edge r59) (a 19) (a 27) 0 t9 c59 (by decide +kernel)
  have t15 : a 19 ∈ [4] := remove (a 19) 0 [0,4] d19 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t12 (And.intro t13 (And.intro t14 (t15)))))))))))))))

theorem chunk11 (a : Nat → Nat)
    (d23 : a 23 ∈ [0,4])
    (d31 : a 31 ∈ [2])
    (d25 : a 25 ∈ [0,6])
    (d24 : a 24 ∈ [3])
    (d30 : a 30 ∈ [0,4])
    (d26 : a 26 ∈ [4])
    (d4 : a 4 ∈ [0,2])
    (d12 : a 12 ∈ [2])
    (d5 : a 5 ∈ [0,1])
    (d13 : a 13 ∈ [1])
    (d9 : a 9 ∈ [0,4])
    (d8 : a 8 ∈ [1])
    (d17 : a 17 ∈ [0,6])
    (d16 : a 16 ∈ [3])
    (d21 : a 21 ∈ [0,3])
    (d22 : a 22 ∈ [0,4])
    (c18 : edge r18 (a 4) (a 12)=true)
    (c21 : edge r21 (a 5) (a 13)=true)
    (c28 : edge r28 (a 8) (a 9)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c53 : edge r53 (a 17) (a 21)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c68 : edge r68 (a 24) (a 25)=true)
    (c74 : edge r74 (a 26) (a 30)=true)
    : a 23 ∈ [4] ∧ a 25 ∈ [6] ∧ a 30 ∈ [4] ∧ a 4 ∈ [2] ∧ a 5 ∈ [1] ∧ a 9 ∈ [4] ∧ a 17 ∈ [6] ∧ a 21 ∈ [3] ∧ a 22 ∈ [4] := by
  have b0 : a 23 ≠ 0 := exclude [2] (edge r67) (a 23) (a 31) 0 d31 c67 (by decide +kernel)
  have t0 : a 23 ∈ [4] := remove (a 23) 0 [0,4] d23 b0
  have b1 : a 25 ≠ 0 := exclude [3] (fun u v => edge r68 v u) (a 25) (a 24) 0 d24 c68 (by decide +kernel)
  have t1 : a 25 ∈ [6] := remove (a 25) 0 [0,6] d25 b1
  have b2 : a 30 ≠ 0 := exclude [4] (fun u v => edge r74 v u) (a 30) (a 26) 0 d26 c74 (by decide +kernel)
  have t2 : a 30 ∈ [4] := remove (a 30) 0 [0,4] d30 b2
  have b3 : a 4 ≠ 0 := exclude [2] (edge r18) (a 4) (a 12) 0 d12 c18 (by decide +kernel)
  have t3 : a 4 ∈ [2] := remove (a 4) 0 [0,2] d4 b3
  have b4 : a 5 ≠ 0 := exclude [1] (edge r21) (a 5) (a 13) 0 d13 c21 (by decide +kernel)
  have t4 : a 5 ∈ [1] := remove (a 5) 0 [0,1] d5 b4
  have b5 : a 9 ≠ 0 := exclude [1] (fun u v => edge r28 v u) (a 9) (a 8) 0 d8 c28 (by decide +kernel)
  have t5 : a 9 ∈ [4] := remove (a 9) 0 [0,4] d9 b5
  have b6 : a 17 ≠ 0 := exclude [3] (fun u v => edge r48 v u) (a 17) (a 16) 0 d16 c48 (by decide +kernel)
  have t6 : a 17 ∈ [6] := remove (a 17) 0 [0,6] d17 b6
  have b7 : a 21 ≠ 0 := exclude [6] (fun u v => edge r53 v u) (a 21) (a 17) 0 t6 c53 (by decide +kernel)
  have t7 : a 21 ∈ [3] := remove (a 21) 0 [0,3] d21 b7
  have b8 : a 22 ≠ 0 := exclude [4] (edge r65) (a 22) (a 23) 0 t0 c65 (by decide +kernel)
  have t8 : a 22 ∈ [4] := remove (a 22) 0 [0,4] d22 b8
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (t8))))))))
#print axioms chunk8
#print axioms chunk9
#print axioms chunk10
#print axioms chunk11
end PartitionCover205_199
