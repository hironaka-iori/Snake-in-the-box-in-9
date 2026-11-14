import PartitionData205_169
namespace PartitionCover205_169
open FiniteDomain205
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem chunk12 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,2])
    (d27 : a 27 ∈ [0])
    (d28 : a 28 ∈ [0,1])
    (d20 : a 20 ∈ [0])
    (d23 : a 23 ∈ [0,4])
    (d22 : a 22 ∈ [0])
    (d31 : a 31 ∈ [0,1])
    (d29 : a 29 ∈ [0,1])
    (d8 : a 8 ∈ [0,5])
    (d10 : a 10 ∈ [0])
    (d9 : a 9 ∈ [0,5])
    (d11 : a 11 ∈ [0])
    (d17 : a 17 ∈ [0,5])
    (d16 : a 16 ∈ [0])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 19 ∈ [0] ∧ a 28 ∈ [0] ∧ a 23 ∈ [0] ∧ a 31 ∈ [0] ∧ a 29 ∈ [0] ∧ a 8 ∈ [0] ∧ a 9 ∈ [0] ∧ a 17 ∈ [0] := by
  have b0 : a 19 ≠ 2 := exclude [0] (edge r59) (a 19) (a 27) 2 d27 c59 (by decide +kernel)
  have t0 : a 19 ∈ [0] := remove (a 19) 2 [0,2] d19 b0
  have b1 : a 28 ≠ 1 := exclude [0] (fun u v => edge r62 v u) (a 28) (a 20) 1 d20 c62 (by decide +kernel)
  have t1 : a 28 ∈ [0] := remove (a 28) 1 [0,1] d28 b1
  have b2 : a 23 ≠ 4 := exclude [0] (fun u v => edge r65 v u) (a 23) (a 22) 4 d22 c65 (by decide +kernel)
  have t2 : a 23 ∈ [0] := remove (a 23) 4 [0,4] d23 b2
  have b3 : a 31 ≠ 1 := exclude [0] (fun u v => edge r67 v u) (a 31) (a 23) 1 t2 c67 (by decide +kernel)
  have t3 : a 31 ∈ [0] := remove (a 31) 1 [0,1] d31 b3
  have b4 : a 29 ≠ 1 := exclude [0] (fun u v => edge r76 v u) (a 29) (a 28) 1 t1 c76 (by decide +kernel)
  have t4 : a 29 ∈ [0] := remove (a 29) 1 [0,1] d29 b4
  have b5 : a 8 ≠ 5 := exclude [0] (edge r29) (a 8) (a 10) 5 d10 c29 (by decide +kernel)
  have t5 : a 8 ∈ [0] := remove (a 8) 5 [0,5] d8 b5
  have b6 : a 9 ≠ 5 := exclude [0] (edge r32) (a 9) (a 11) 5 d11 c32 (by decide +kernel)
  have t6 : a 9 ∈ [0] := remove (a 9) 5 [0,5] d9 b6
  have b7 : a 17 ≠ 5 := exclude [0] (fun u v => edge r48 v u) (a 17) (a 16) 5 d16 c48 (by decide +kernel)
  have t7 : a 17 ∈ [0] := remove (a 17) 5 [0,5] d17 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))

theorem chunk13 (a : Nat → Nat)
    (d5 : a 5 ∈ [0,13])
    (d4 : a 4 ∈ [7])
    (d6 : a 6 ∈ [0,2])
    (d20 : a 20 ∈ [0,8])
    (d7 : a 7 ∈ [0,2])
    (d14 : a 14 ∈ [0,1])
    (d22 : a 22 ∈ [0,4])
    (d15 : a 15 ∈ [0,5])
    (d10 : a 10 ∈ [0,5])
    (d26 : a 26 ∈ [0,5])
    (d11 : a 11 ∈ [0,5])
    (d27 : a 27 ∈ [0,1])
    (d30 : a 30 ∈ [0,2])
    (d31 : a 31 ∈ [0,1,2,3])
    (d16 : a 16 ∈ [0,5])
    (d18 : a 18 ∈ [0,2])
    (c16 : edge r16 (a 4) (a 5)=true)
    (c17 : edge r17 (a 4) (a 6)=true)
    (c19 : edge r19 (a 4) (a 20)=true)
    (c20 : edge r20 (a 5) (a 7)=true)
    (c24 : edge r24 (a 6) (a 14)=true)
    (c25 : edge r25 (a 6) (a 22)=true)
    (c26 : edge r26 (a 7) (a 15)=true)
    (c36 : edge r36 (a 10) (a 14)=true)
    (c37 : edge r37 (a 10) (a 26)=true)
    (c38 : edge r38 (a 11) (a 15)=true)
    (c39 : edge r39 (a 11) (a 27)=true)
    (c46 : edge r46 (a 14) (a 30)=true)
    (c47 : edge r47 (a 15) (a 31)=true)
    (c50 : edge r50 (a 16) (a 20)=true)
    (c56 : edge r56 (a 18) (a 22)=true)
    : a 5 ∈ [13] ∧ a 6 ∈ [2] ∧ a 20 ∈ [8] ∧ a 7 ∈ [2] ∧ a 14 ∈ [1] ∧ a 22 ∈ [4] ∧ a 15 ∈ [5] ∧ a 10 ∈ [5] ∧ a 26 ∈ [5] ∧ a 11 ∈ [5] ∧ a 27 ∈ [1] ∧ a 30 ∈ [2] ∧ a 31 ∈ [2,3] ∧ a 16 ∈ [5] ∧ a 18 ∈ [2] := by
  have b0 : a 5 ≠ 0 := exclude [7] (fun u v => edge r16 v u) (a 5) (a 4) 0 d4 c16 (by decide +kernel)
  have t0 : a 5 ∈ [13] := remove (a 5) 0 [0,13] d5 b0
  have b1 : a 6 ≠ 0 := exclude [7] (fun u v => edge r17 v u) (a 6) (a 4) 0 d4 c17 (by decide +kernel)
  have t1 : a 6 ∈ [2] := remove (a 6) 0 [0,2] d6 b1
  have b2 : a 20 ≠ 0 := exclude [7] (fun u v => edge r19 v u) (a 20) (a 4) 0 d4 c19 (by decide +kernel)
  have t2 : a 20 ∈ [8] := remove (a 20) 0 [0,8] d20 b2
  have b3 : a 7 ≠ 0 := exclude [13] (fun u v => edge r20 v u) (a 7) (a 5) 0 t0 c20 (by decide +kernel)
  have t3 : a 7 ∈ [2] := remove (a 7) 0 [0,2] d7 b3
  have b4 : a 14 ≠ 0 := exclude [2] (fun u v => edge r24 v u) (a 14) (a 6) 0 t1 c24 (by decide +kernel)
  have t4 : a 14 ∈ [1] := remove (a 14) 0 [0,1] d14 b4
  have b5 : a 22 ≠ 0 := exclude [2] (fun u v => edge r25 v u) (a 22) (a 6) 0 t1 c25 (by decide +kernel)
  have t5 : a 22 ∈ [4] := remove (a 22) 0 [0,4] d22 b5
  have b6 : a 15 ≠ 0 := exclude [2] (fun u v => edge r26 v u) (a 15) (a 7) 0 t3 c26 (by decide +kernel)
  have t6 : a 15 ∈ [5] := remove (a 15) 0 [0,5] d15 b6
  have b7 : a 10 ≠ 0 := exclude [1] (edge r36) (a 10) (a 14) 0 t4 c36 (by decide +kernel)
  have t7 : a 10 ∈ [5] := remove (a 10) 0 [0,5] d10 b7
  have b8 : a 26 ≠ 0 := exclude [5] (fun u v => edge r37 v u) (a 26) (a 10) 0 t7 c37 (by decide +kernel)
  have t8 : a 26 ∈ [5] := remove (a 26) 0 [0,5] d26 b8
  have b9 : a 11 ≠ 0 := exclude [5] (edge r38) (a 11) (a 15) 0 t6 c38 (by decide +kernel)
  have t9 : a 11 ∈ [5] := remove (a 11) 0 [0,5] d11 b9
  have b10 : a 27 ≠ 0 := exclude [5] (fun u v => edge r39 v u) (a 27) (a 11) 0 t9 c39 (by decide +kernel)
  have t10 : a 27 ∈ [1] := remove (a 27) 0 [0,1] d27 b10
  have b11 : a 30 ≠ 0 := exclude [1] (fun u v => edge r46 v u) (a 30) (a 14) 0 t4 c46 (by decide +kernel)
  have t11 : a 30 ∈ [2] := remove (a 30) 0 [0,2] d30 b11
  have b12 : a 31 ≠ 0 := exclude [5] (fun u v => edge r47 v u) (a 31) (a 15) 0 t6 c47 (by decide +kernel)
  have t12 : a 31 ∈ [1,2,3] := remove (a 31) 0 [0,1,2,3] d31 b12
  have b13 : a 31 ≠ 1 := exclude [5] (fun u v => edge r47 v u) (a 31) (a 15) 1 t6 c47 (by decide +kernel)
  have t13 : a 31 ∈ [2,3] := remove (a 31) 1 [1,2,3] t12 b13
  have b14 : a 16 ≠ 0 := exclude [8] (edge r50) (a 16) (a 20) 0 t2 c50 (by decide +kernel)
  have t14 : a 16 ∈ [5] := remove (a 16) 0 [0,5] d16 b14
  have b15 : a 18 ≠ 0 := exclude [4] (edge r56) (a 18) (a 22) 0 t5 c56 (by decide +kernel)
  have t15 : a 18 ∈ [2] := remove (a 18) 0 [0,2] d18 b15
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (And.intro t7 (And.intro t8 (And.intro t9 (And.intro t10 (And.intro t11 (And.intro t13 (And.intro t14 (t15))))))))))))))

theorem chunk14 (a : Nat → Nat)
    (d19 : a 19 ∈ [0,2])
    (d27 : a 27 ∈ [1])
    (d28 : a 28 ∈ [0,1])
    (d20 : a 20 ∈ [8])
    (d23 : a 23 ∈ [0,4])
    (d22 : a 22 ∈ [4])
    (d31 : a 31 ∈ [2,3])
    (d29 : a 29 ∈ [0,1])
    (d8 : a 8 ∈ [0,5])
    (d10 : a 10 ∈ [5])
    (d9 : a 9 ∈ [0,5])
    (d11 : a 11 ∈ [5])
    (d17 : a 17 ∈ [0,5])
    (d16 : a 16 ∈ [5])
    (c29 : edge r29 (a 8) (a 10)=true)
    (c32 : edge r32 (a 9) (a 11)=true)
    (c48 : edge r48 (a 16) (a 17)=true)
    (c59 : edge r59 (a 19) (a 27)=true)
    (c62 : edge r62 (a 20) (a 28)=true)
    (c65 : edge r65 (a 22) (a 23)=true)
    (c67 : edge r67 (a 23) (a 31)=true)
    (c76 : edge r76 (a 28) (a 29)=true)
    : a 19 ∈ [2] ∧ a 28 ∈ [1] ∧ a 23 ∈ [4] ∧ a 31 ∈ [2] ∧ a 29 ∈ [1] ∧ a 8 ∈ [5] ∧ a 9 ∈ [5] ∧ a 17 ∈ [5] := by
  have b0 : a 19 ≠ 0 := exclude [1] (edge r59) (a 19) (a 27) 0 d27 c59 (by decide +kernel)
  have t0 : a 19 ∈ [2] := remove (a 19) 0 [0,2] d19 b0
  have b1 : a 28 ≠ 0 := exclude [8] (fun u v => edge r62 v u) (a 28) (a 20) 0 d20 c62 (by decide +kernel)
  have t1 : a 28 ∈ [1] := remove (a 28) 0 [0,1] d28 b1
  have b2 : a 23 ≠ 0 := exclude [4] (fun u v => edge r65 v u) (a 23) (a 22) 0 d22 c65 (by decide +kernel)
  have t2 : a 23 ∈ [4] := remove (a 23) 0 [0,4] d23 b2
  have b3 : a 31 ≠ 3 := exclude [4] (fun u v => edge r67 v u) (a 31) (a 23) 3 t2 c67 (by decide +kernel)
  have t3 : a 31 ∈ [2] := remove (a 31) 3 [2,3] d31 b3
  have b4 : a 29 ≠ 0 := exclude [1] (fun u v => edge r76 v u) (a 29) (a 28) 0 t1 c76 (by decide +kernel)
  have t4 : a 29 ∈ [1] := remove (a 29) 0 [0,1] d29 b4
  have b5 : a 8 ≠ 0 := exclude [5] (edge r29) (a 8) (a 10) 0 d10 c29 (by decide +kernel)
  have t5 : a 8 ∈ [5] := remove (a 8) 0 [0,5] d8 b5
  have b6 : a 9 ≠ 0 := exclude [5] (edge r32) (a 9) (a 11) 0 d11 c32 (by decide +kernel)
  have t6 : a 9 ∈ [5] := remove (a 9) 0 [0,5] d9 b6
  have b7 : a 17 ≠ 0 := exclude [5] (fun u v => edge r48 v u) (a 17) (a 16) 0 d16 c48 (by decide +kernel)
  have t7 : a 17 ∈ [5] := remove (a 17) 0 [0,5] d17 b7
  exact And.intro t0 (And.intro t1 (And.intro t2 (And.intro t3 (And.intro t4 (And.intro t5 (And.intro t6 (t7)))))))
#print axioms chunk12
#print axioms chunk13
#print axioms chunk14
end PartitionCover205_169
